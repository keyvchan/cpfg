import z3
from rich.logging import RichHandler
import logging

FORMAT = "%( message )s"
logging.basicConfig(level="DEBUG", datefmt="[%X]", handlers=[RichHandler(markup=True)])
log = logging.getLogger("io")


class Propgation:

    # useful variables
    high_function = None
    ops = None
    decomplib = None

    # package
    pcode = None
    symbol = None

    # flat api
    getByte = None
    getDataAt = None
    getFunctionAt = None
    getFunctionContaining = None
    getInstructionAt = None
    getInstructionContaining = None
    getInt = None
    getReferencesTo = None
    getSymbolAt = None

    cast_functions = ["_atoi", "_itoa"]

    # constant
    INT_MAX = 2147483647

    # global variables
    handled_INDIRECT = []
    INDIRECT_list = []

    def __init__(self, high_function, ops, imported_dict):
        self.high_function = high_function
        self.ops = ops
        if "decomplib" in imported_dict:
            self.decomplib = imported_dict["decomplib"]

        if "pcode" in imported_dict:
            self.pcode = imported_dict["pcode"]
        if "symbol" in imported_dict:
            self.symbol = imported_dict["symbol"]

        if "getByte" in imported_dict:
            self.getByte = imported_dict["getByte"]
        if "getDataAt" in imported_dict:
            self.getDataAt = imported_dict["getDataAt"]
        if "getFunctionAt" in imported_dict:
            self.getFunctionAt = imported_dict["getFunctionAt"]
        if "getFunctionContaining" in imported_dict:
            self.getFunctionContaining = imported_dict["getFunctionContaining"]
        if "getInstructionAt" in imported_dict:
            self.getInstructionAt = imported_dict["getInstructionAt"]
        if "getInstructionContaining" in imported_dict:
            self.getInstructionContaining = imported_dict["getInstructionContaining"]
        if "getInt" in imported_dict:
            self.getInt = imported_dict["getInt"]
        if "getReferencesTo" in imported_dict:
            self.getReferencesTo = imported_dict["getReferencesTo"]
        if "getSymbolAt" in imported_dict:
            self.getSymbolAt = imported_dict["getSymbolAt"]

    def get_INDIRECT_operation(self, indirect_operation):
        log.info("Get a INDIRECT operation: %s", indirect_operation)

        seqnum = self.pcode.SequenceNumber(
            indirect_operation.getInput(0).getPCAddress(),
            indirect_operation.getInput(1).getOffset(),
        )
        ops = self.high_function.getPcodeOps(seqnum.getTarget())
        return ops

    def handle_Constant(self, input, s: z3.Solver, x):
        log.info("handle constant: %s", input)

        y = z3.BitVec(input.toString(), input.getSize() * 8)
        s.add(x == y, y == input.getOffset())
        status = s.check()
        if status == z3.sat:
            log.debug("path: \n %s", s)
            result = s.model().eval(x)

            return result
        else:
            log.error("Not sat, may be a bug: %s", s)

    def handle_INDIRECT(self, last_operation, s, x):
        log.info("handle indirect: %s", last_operation)
        # Check the right value is a constant
        if last_operation.getInput(0).isConstant():
            return self.handle_Constant(last_operation.getInput(0), s, x)
        else:
            y = z3.BitVec(
                last_operation.getInput(0).toString(),
                last_operation.getInput(0).getSize() * 8,
            )
            block = last_operation.getParent()
            iter = block.getIterator()
            for op1 in iter:
                if op1.getOpcode() == self.pcode.PcodeOp.CALL:
                    func = self.getFunctionAt(op1.getInput(0).getAddress())
                    if func.getName() == "_fscanf":
                        log.debug(
                            "The INDIRECT is in the same block of this call: %s, which is can not be trusted",
                            func,
                        )
                        s.add(y == self.INT_MAX)
                        return self.INT_MAX

            s.add(x == y)
            return self.propgation(last_operation.getInput(0), s, y)

    def handle_COPY(self, last_operation, s, x):
        log.info("Handle COPY: %s", last_operation)

        # Check the right value is a constant
        if last_operation.getInput(0).isConstant():
            return self.handle_Constant(last_operation.getInput(0), s, x)
        else:
            y = z3.BitVec(
                last_operation.getInput(0).toString(),
                last_operation.getInput(0).getSize() * 8,
            )
            s.add(x == y)
            return self.propgation(last_operation.getInput(0), s, y)

    def check_condition(self, input):
        last_operation = input.getDef()
        input0 = last_operation.getInput(0)
        input1 = last_operation.getInput(1)
        y = z3.BitVec(input0.toString(), input0.getSize() * 8)
        z = z3.BitVec(input1.toString(), input1.getSize() * 8)
        s = z3.Solver()
        if last_operation.getOpcode() == self.pcode.PcodeOp.INT_SLESS:
            value = self.propgation(last_operation.getInput(0), s, y)
            s.add(y < z, y == value, z == input1.getOffset())
            if s.check() == z3.sat:
                result = s.model().eval(z3.ULT(y, z))
                log.debug("s < z is %s", result)
                return result
        elif last_operation.getOpcode() == self.pcode.PcodeOp.INT_NOTEQUAL:
            value = self.propgation(last_operation.getInput(0), s, y)
            s.add(y != z, y == value, z == input1.getOffset())
            if s.check() == z3.sat:
                result = s.model().eval(y != z)
                log.debug("s != z is %s", result)
                return result
        elif last_operation.getOpcode() == self.pcode.PcodeOp.INT_EQUAL:
            value = self.propgation(last_operation.getInput(0), s, y)
            s.add(y == z, y == value, z == input1.getOffset())
            if s.check() == z3.sat:
                result = s.model().eval(y == z)
                log.debug("s == z is %s", result)
                return result

        else:
            log.error("Not implementated yet")

    # TODO: need more attentation.
    def handle_MULTIEQUAL(self, last_operation, s: z3.Solver, x):
        log.info("handle MULTIEQUAL: %s", last_operation)

        log.debug("Checking if need branch analysis...")

        # check if a input comes from a branch.
        last_block = None
        for input in last_operation.getInputs():
            log.debug("Checking %s", input)

            defination_of_input = input.getDef()
            if defination_of_input != None:
                block = defination_of_input.getParent()
                if block.getInSize() == 1:

                    stop_op = None
                    # print(op.getParent().getIn(0))
                    iter = block.getIn(0).getIterator()
                    for op1 in iter:
                        stop_op = op1
                        # print(stop_op)
                    if stop_op.getOpcode() == self.pcode.PcodeOp.CBRANCH:
                        log.debug("Found a cbranch")

                        result = self.check_condition(stop_op.getInput(1))
                        if result == True:
                            log.debug(
                                "condition is true, start branch analysis, this input is valid"
                            )
                            if last_block != None:
                                if last_block != block:
                                    if block.calcDepth(last_block) < 0:
                                        log.debug("depth < 0, it is a succcesser block")
                                        # print("depth: ", block.calcDepth(last_block))
                                        s.push()
                                        result = self.propgation(input, s, x)
                                        if result != None:
                                            log.info(
                                                "%s has a value %s, previous value will be replaced",
                                                input,
                                                result,
                                            )
                                            value = result

                                        s.pop()
                                    else:
                                        log.info("depth > 0, ignore this input")
                            else:
                                log.info(
                                    "last_block is None, %s is the first input", input
                                )
                                s.push()
                                result = self.propgation(input, s, x)
                                if result != None:
                                    value = result
                                s.pop()
                                last_block = block

                        else:
                            log.info("condition is True, no need for branch analysis")
                            s.push()
                            result = self.propgation(input, s, x)
                            if result != None:
                                value = result
                            s.pop()
                            last_block = block
                    else:
                        log.info("input not from cbranch, do the normal analysis")
                        s.push()
                        result = self.propgation(input, s, x)
                        if result != None:
                            value = result
                        s.pop()
                        last_block = block

                else:
                    log.info(
                        "block has multiple or zero in blocks, it could be a entry block"
                    )
                    s.push()
                    result = self.propgation(input, s, x)
                    if result != None:
                        value = result
                    s.pop()
                last_block = block
            else:
                log.info("last operation is None")

        log.debug("Output of multiequal %s is %s", last_operation.getOutput(), value)

        s.add(x == value)

        return value

    def handle_Unique(self, operation, s, x):
        log.error("Not implementated yet: %s", operation)

    def handle_CALL(self, operation, s, x):
        log.info("handle function CALL: %s", operation)

        # print("Found CALL: ", s)
        f = self.getFunctionAt(operation.getInput(0).getAddress())
        log.debug("The function is %s", f)

        if f.getName() in self.cast_functions:
            log.debug("Data cast occured: %s", f.getName())
            if operation.getInput(1).isConstant():
                return self.handle_Constant(operation.getInput(1), s, x)
            if operation.getInput(1).isUnique():
                return self.handle_Unique(operation.getInput(1), s, x)
            else:
                log.error("Not covered yet")

        if f.getName() == "_socket":
            log.debug(
                "call builtin function %s which return value can't be decided",
                f.getName(),
            )
            return False
        if f.getName() == "_recv":
            log.debug(
                "call builtin function %s which return value can't be decided",
                f.getName(),
            )
            return False
        if f.getName() == "_connect":
            log.debug(
                "call builtin function %s which return value can't be decided",
                f.getName(),
            )
            return True

        else:
            opiter = self.high_function.getPcodeOps()
            while opiter.hasNext():
                op = opiter.next()
                if op.getOpcode() == self.pcode.PcodeOp.RETURN:
                    log.debug("Found RETURN: %s", op)
                    if op.getNumInputs() > 1:
                        if op.getInput(1).isConstant():
                            return self.handle_Constant(op.getInput(1), s, x)

                        # TODO: hadnle address
                        elif op.getInput(1).isAddress():
                            log.warning("Found a address, do nothing for now.")
                            return self.handle_Address(op.getInput(1), s, x)
                        elif op.getInput(1).isRegister():
                            log.warning("It is parameter: %s", op.getInput(1))
                            return self.propgation(op.getInput(1), s, x)
                    else:
                        log.error("not covered yet")

    def handle_Address(self, input, s, x):
        log.info("handle address: %s", input)

        address = input.getAddress()

        out = self.getReferencesTo(address)
        for element in out:
            if element.getReferenceType() == self.symbol.DataRefType.WRITE:
                if element.isOperandReference():

                    f1 = self.getFunctionContaining(element.getFromAddress())

                    log.warning("current function: %s", f1)
                    instruct = self.getInstructionContaining(element.getFromAddress())
                    # op1 = instruct.getPcode()[element.getOperandIndex()]

                    res = self.decomplib.decompileFunction(f1, 60, monitor)
                    high = res.getHighFunction()
                    ops = high.getPcodeOps(instruct.getAddress())
                    for i in ops:
                        result = self.propgation(i.getInput(0), s, x)
                        return result
        log.debug("No write, may ba a pre-defined global variable")

        # TODO: Found a way to get the data of a global variable.
        # TODO: We assume that the data here is a integer, so read it by using getByte
        value = self.getByte(input.getAddress())
        log.debug("The value in %s is %s", input, value)
        return value

    def propgation(self, varnode, s: z3.Solver, x):
        log.info("Propgation on %s", varnode)
        last_operation = varnode.getDef()
        log.debug("Last operation is %s: ", last_operation)

        if last_operation != None:
            op_code = last_operation.getOpcode()
            if op_code == self.pcode.PcodeOp.INDIRECT:
                return self.handle_INDIRECT(last_operation, s, x)
            elif op_code == self.pcode.PcodeOp.COPY:
                return self.handle_COPY(last_operation, s, x)
            elif op_code == self.pcode.PcodeOp.MULTIEQUAL:
                return self.handle_MULTIEQUAL(last_operation, s, x)
            elif op_code == self.pcode.PcodeOp.CALL:
                return self.handle_CALL(last_operation, s, x)
            else:
                log.error("Not implementated yet: %s", last_operation.getMnemonic())
        else:
            if varnode.isAddress():
                return self.handle_address(varnode, s, x)
            log.error("last_operation is None, not implementated yet")
        return 0

    def constant_propgation(self, varnode, operation):
        # taking consider of all indirect operation

        s = z3.Solver()
        x = z3.BitVec(varnode.toString(), varnode.getSize() * 8)

        # 1. get all INDIRECT that may effect this value
        log.info("Checking INDIRECT releated to this varnode: %s", varnode)
        vs = varnode.getHigh().getInstances()
        for v in vs:
            for desc in v.getDescendants():
                if desc.getOpcode() == self.pcode.PcodeOp.INDIRECT:
                    log.debug("It's a INDIRECT, add it to INDIRECT_list: %s", desc)
                    self.INDIRECT_list.append(desc)
                else:
                    log.debug("It's not a INDIRECT: %s", desc)

        for operation in self.INDIRECT_list:
            ops = self.get_INDIRECT_operation(operation)
            for _, op in enumerate(ops):
                if op.getOpcode() == self.pcode.PcodeOp.CALL:
                    func = self.getFunctionAt(op.getInput(0).getAddress())
                    log.info("Found a call: %s", func)
                    if func.getName() == "_fscanf":
                        log.debug(
                            "This function call can not be trusted: %s, so the value should be set to maxium",
                            func,
                        )
                        return self.INT_MAX
                    else:
                        log.debug("This function call can be trusted: %s", func)
                else:
                    log.debug("It's not a CALL, ignore it: %s", op)

        log.debug("reaching this point")
        # User input source not found, fallback to normal analysis.
        result = self.propgation(varnode, s, x)
        return result
