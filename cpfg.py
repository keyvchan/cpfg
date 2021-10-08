import z3
from rich.logging import RichHandler
import logging


FORMAT = "%( message )s"
logging.basicConfig(level="DEBUG", datefmt="[%X]", handlers=[RichHandler(markup=True)])
log = logging.getLogger("cpfg")

# Assume Uncertain is true
class Uncertain:
    pass


uncertain = Uncertain()


class Propgation:

    # useful variables
    high_function = None
    ops = None
    decomplib = None
    monitor = None
    func = None

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

    def __init__(self, high_function, ops, func, imported_dict):
        self.high_function = high_function
        self.ops = ops
        self.func = func

        if "decomplib" in imported_dict:
            self.decomplib = imported_dict["decomplib"]
        if "monitor" in imported_dict:
            self.monitor = imported_dict["monitor"]

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

    def decompile(self, func):

        res = self.decomplib.decompileFunction(func, 60, self.monitor)
        high = res.getHighFunction()
        return high

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

        # A very clumsy way to fit the size requirement, should do better.
        if x.size() != y.size():
            s.add(z3.ZeroExt(y.size() - x.size(), x) == y, y == input.getOffset())
        else:
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
            return self.propgation(last_operation.getInput(0), last_operation, s, y)

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
            return self.propgation(last_operation.getInput(0), last_operation, s, y)

    def check_condition(self, input, original_op):
        log.info("Checking condition of %s", input)
        last_operation = input.getDef()
        log.info("Last operation is %s: ", last_operation)

        input0 = last_operation.getInput(0)
        input1 = last_operation.getInput(1)
        y = z3.BitVec(input0.toString(), input0.getSize() * 8)
        z = z3.BitVec(input1.toString(), input1.getSize() * 8)
        s = z3.Solver()

        if last_operation.getOpcode() == self.pcode.PcodeOp.INT_SLESS:
            log.info("It is a INT_SLESS, checking %s < %s", y, z)
            value = self.propgation(last_operation.getInput(0), last_operation, s, y)
            s.add(y < z, y == value, z == input1.getOffset())
            if s.check() == z3.sat:
                result = s.model().eval(z3.ULT(y, z))
                log.debug("%s < %s is %s", y, z, result)
                return result
        elif last_operation.getOpcode() == self.pcode.PcodeOp.INT_NOTEQUAL:
            log.info("It is a INT_NOTEQUAL, checking %s < %s", y, z)
            value = self.propgation(last_operation.getInput(0), last_operation, s, y)
            if isinstance(value, Uncertain):
                log.debug("The value can't be determained")
                return uncertain
            else:
                s.add(y != z, y == value, z == input1.getOffset())
                if s.check() == z3.sat:
                    result = s.model().eval(y != z)
                    log.debug("%s != %s is %s", y, z, result)
                    return result
        elif last_operation.getOpcode() == self.pcode.PcodeOp.INT_EQUAL:
            log.info("It is a INT_EQUAL, checking %s < %s", y, z)
            value = self.propgation(last_operation.getInput(0), last_operation, s, y)

            if isinstance(value, Uncertain):
                log.debug("The value can't be determained")
                return uncertain
            else:
                s.add(y == z, y == value, z == input1.getOffset())
                if s.check() == z3.sat:
                    result = s.model().eval(y == z)
                    log.debug("%s == %s is %s", y, z, result)
                    return result

        else:
            log.error("Not implementated yet")

    # TODO: need more attentation.
    def handle_MULTIEQUAL(self, last_operation, s: z3.Solver, x):
        log.info("handle MULTIEQUAL: %s", last_operation)

        log.debug("Checking if need branch analysis...")

        # check if a input comes from a branch.
        value = None
        uncertain_values = []
        last_block = None
        for input in last_operation.getInputs():
            log.debug("Checking %s", input)

            defination_of_input = input.getDef()
            if defination_of_input != None:
                block = defination_of_input.getParent()
                log.debug("The block of %s is %s", defination_of_input, block)
                iter = block.getIterator()
                # for op1 in iter:

                #     stop_op = op1
                #     print(stop_op.getSeqnum(), stop_op)
                # print(" ")
                if block.getInSize() == 1:

                    stop_op = None
                    # print(op.getParent().getIn(0))
                    iter = block.getIn(0).getIterator()
                    for op1 in iter:

                        stop_op = op1
                    #     print(stop_op.getSeqnum(), stop_op)
                    if stop_op.getOpcode() == self.pcode.PcodeOp.CBRANCH:
                        log.debug("Found a cbranch: %s", stop_op)

                        result = self.check_condition(stop_op.getInput(1), None)
                        if result == True:
                            log.debug(
                                "condition is True, start branch analysis, this input is valid"
                            )
                            if last_block != None:
                                if last_block != block:
                                    # print(block.calcDepth(last_block))
                                    if block.calcDepth(last_block) < 0:
                                        log.debug("depth < 0, it is a succcesser block")
                                        # print("depth: ", block.calcDepth(last_block))
                                        s.push()
                                        result = self.propgation(
                                            input, last_operation, s, x
                                        )
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
                                result = self.propgation(input, last_operation, s, x)
                                if result != None:
                                    value = result
                                s.pop()
                                last_block = block

                        elif isinstance(result, Uncertain):
                            log.info(
                                "The condition is uncertain, need to perserve the value"
                            )
                            s.push()
                            result = self.propgation(input, last_operation, s, x)
                            if result != None:
                                uncertain_values.append(result)
                            s.pop()
                            last_block = block

                        else:
                            log.info(
                                "condition is False, no need for branch analysis, and this input can be ignore"
                            )
                            # s.push()
                            # result = self.propgation(input, s, x)
                            # if result != None:
                            #     value = result
                            # s.pop()
                            # last_block = block
                    else:
                        log.info("input not from cbranch, do the normal analysis")
                        s.push()
                        result = self.propgation(input, last_operation, s, x)
                        if result != None:
                            value = result
                        s.pop()
                        last_block = block

                else:
                    log.info(
                        "block has multiple or zero in blocks, it could be a entry block"
                    )
                    s.push()
                    result = self.propgation(input, last_operation, s, x)
                    if result != None:
                        value = result
                    s.pop()
                last_block = block
            else:
                log.info("last operation is None")

        if uncertain_values != None:

            if value in uncertain_values:
                log.info("value in uncertain_values, found the maxium")
            else:

                # TODO: Rewrite it when avaiable
                if value == None:
                    value = 0
                if not isinstance(value, int):
                    value = value.as_long()

                log.info("value not in uncertain_values, found the maxium")
                # simple bubble sort
                for i in uncertain_values:
                    if isinstance(i, int):
                        if value < i:
                            value = i
                    else:
                        log.debug("Data conversion")
                        if value < i.as_long():
                            value = i

        else:
            log.info("Uncertain value is None")

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
            high_function = self.decompile(f)
            opiter = high_function.getPcodeOps()
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
                            return self.propgation(op.getInput(1), op, s, x)
                    elif op.getNumInputs() == 1:
                        if op.getInput(0).isConstant():
                            log.info(
                                "The return don't have a return value, it may be a bad function call."
                            )
                        return uncertain
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

                    high = self.decompile(f1)
                    ops = high.getPcodeOps(instruct.getAddress())
                    for i in ops:
                        result = self.propgation(i.getInput(0), i, s, x)
                        return result
        log.debug("No write, may ba a pre-defined global variable")

        # TODO: Found a way to get the data of a global variable.
        # TODO: We assume that the data here is a integer, so read it by using getByte
        value = self.getByte(input.getAddress())
        log.debug("The value in %s is %s", input, value)
        return value

    def handle_LOAD(self, operation, s, x):
        log.info("handle LOAD: %s", operation)

        # Found store in current function
        # The most simple case, there is only one STORE in function
        # TODO: Make it more generic
        ops = self.high_function.getPcodeOps()
        for op in ops:
            if op.getOpcode() == self.pcode.PcodeOp.STORE:
                log.debug("Found the store in current function")
                return self.propgation(op.getInput(2), operation, s, x)
        log.info("Load not found in current function")

        log.info("Okay, the input is parameter or a global variables, do the rest")
        # Assume the denominator is function's parameter, found cross reference of this function, then trace it
        # TODO: very limited, should cover more edge cases.
        refs = self.getReferencesTo(self.func.getEntryPoint())
        for ref in refs:
            # print(ref)
            if ref.getReferenceType() == self.symbol.RefType.UNCONDITIONAL_CALL:
                fff = self.getFunctionContaining(ref.getFromAddress())
                fffhigh = self.decompile(fff)
                log.debug("Tracing in %s", fff)
                ops = fffhigh.getPcodeOps()
                for op in ops:
                    if op.getOpcode() == self.pcode.PcodeOp.STORE:
                        log.info("Found a store in Paraents function")
                        log.debug("op: %s", op)

                        return self.propgation(op.getInput(2), op, s, x)

                log.debug("Not found a store, use found the indirect instead")
                ops = fffhigh.getPcodeOps()
                for op in ops:
                    # print(op.getSeqnum(), op)
                    if op.getOpcode() == self.pcode.PcodeOp.INDIRECT:
                        op1 = self.get_INDIRECT_operation(op)
                        for opppp in op1:
                            if opppp.getOpcode() == self.pcode.PcodeOp.COPY:
                                return self.handle_COPY(opppp, s, x)
                log.info("Not found INDIRECT either, it could be any value")
                return uncertain

            elif ref.getReferenceType() == self.symbol.RefType.EXTERNAL_REF:
                log.info(
                    "This is a external reference, and the value can't be determained"
                )
                return uncertain
            else:
                log.error("Not cover yet")

    def handle_loop(self, current_operation):
        log.info("Handle loop: %s", current_operation.getParent())
        pass

    def handle_INT_ADD(self, current_operation, s, x):
        log.info("Handle INT_ADD: %s", current_operation)
        input0 = current_operation.getInput(0)
        input1 = current_operation.getInput(1)

        y = z3.BitVec(input1.toString(), input1.getSize() * 8)
        s.add(y == input1.getOffset(), x == x + y)
        return self.propgation(input0, input0.getDef(), s, y)

    def propgation(self, varnode, current_operation, s: z3.Solver, x):
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
            elif op_code == self.pcode.PcodeOp.LOAD:
                return self.handle_LOAD(last_operation, s, x)
            elif op_code == self.pcode.PcodeOp.INT_ADD:
                return self.handle_INT_ADD(last_operation, s, x)
            else:
                log.error("Not impLementated yet: %s", last_operation.getMnemonic())
        else:
            if varnode.isAddress():
                return self.handle_Address(varnode, s, x)
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

        log.debug("INDIRECT is not releated to %s", varnode)
        # User input source not found, fallback to normal analysis.
        result = self.propgation(varnode, operation, s, x)
        return result
