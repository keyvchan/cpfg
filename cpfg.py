import z3
from rich.logging import RichHandler
import typing
import logging


FORMAT = "%( message )s"
logging.basicConfig(level="DEBUG", datefmt="[%X]", handlers=[RichHandler(markup=True)])
log = logging.getLogger("cpfg")

# Assume Uncertain is true

Uncertain = z3.BitVecNumRef


GhidraPackage = typing.Any
GhidraVariable = typing.Any
PcodeOperation = typing.Any
GhidraGlobalFunction = typing.Callable
PcodeVarnode = typing.Any


class Propgation:

    # useful variables
    high_function: GhidraVariable = None
    ops: PcodeOperation = None
    decomplib: GhidraVariable = None
    monitor: GhidraVariable = None
    func: GhidraVariable = None

    # Global variable
    multiequals = {}
    visited_operation = []

    # package
    pcode: GhidraPackage = None
    symbol: GhidraPackage = None

    # flat api
    getByte: GhidraGlobalFunction
    getDataAt: GhidraGlobalFunction
    getFunctionAt: GhidraGlobalFunction
    getFunctionContaining: GhidraGlobalFunction
    getInstructionAt: GhidraGlobalFunction
    getInstructionContaining: GhidraGlobalFunction
    getInt: GhidraGlobalFunction
    getReferencesTo: GhidraGlobalFunction
    getSymbolAt: GhidraGlobalFunction

    cast_functions = ["_atoi", "_itoa"]

    # constant
    INT_MAX: z3.BitVecNumRef
    bit_size = 32
    uncertain: Uncertain

    # global variables
    handled_INDIRECT = []
    INDIRECT_list = []

    def __init__(self, high_function, ops, func, imported_dict, bit_size=32):
        self.high_function = high_function
        self.ops = ops
        self.func = func
        self.bit_size = bit_size

        # max = pow(2, bit_size - 1)
        self.INT_MAX = z3.BitVecVal(0x7FFFFFFF, bit_size)

        self.uncertain = self.INT_MAX

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

    def get_INDIRECT_operation(self, indirect_operation: PcodeOperation):
        log.info("Get a INDIRECT operation: %s", indirect_operation)

        seqnum = self.pcode.SequenceNumber(
            indirect_operation.getInput(0).getPCAddress(),
            indirect_operation.getInput(1).getOffset(),
        )
        ops = self.high_function.getPcodeOps(seqnum.getTarget())
        return ops

    def handle_Constant(
        self, input: PcodeVarnode, s: z3.Solver, x: z3.BitVecRef
    ) -> z3.BitVecNumRef | None:
        log.info("handle constant: %s", input)

        y = z3.BitVec(input.toString(), self.bit_size)

        # A very clumsy way to fit the size requirement, should do better.
        if x.size() != y.size():
            s.add(z3.ZeroExt(y.size() - x.size(), x) == y, y == input.getOffset())
        else:
            s.add(x == y, y == input.getOffset())
        status = s.check()
        if status == z3.sat:
            log.debug("path: \n %s", s)
            result = s.model().eval(x)
            return result.sign_as_bv()

        else:
            log.error("Not sat, may be a bug: %s", s)

    def handle_INDIRECT(
        self,
        last_operation: PcodeOperation,
        s: z3.Solver,
        x: z3.BitVecRef,
        is_in_a_loop: bool,
    ) -> z3.BitVecNumRef | None:
        log.info("handle indirect: %s", last_operation)
        # Check the right value is a constant
        if last_operation.getInput(0).isConstant():
            return self.handle_Constant(last_operation.getInput(0), s, x)
        else:

            input0 = last_operation.getInput(0)

            operations = self.get_INDIRECT_operation(last_operation)
            for _, opppp in enumerate(operations):
                log.debug(opppp)

            y = z3.BitVec(
                last_operation.getInput(0).toString(),
                # last_operation.getInput(0).getSize() * 8,
                self.bit_size,
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

            val = None

            s.push()
            result = self.propgation(input0, input0.getDef(), s, y, is_in_a_loop)

            if result == None:
                val = None
            elif isinstance(result, Uncertain):
                val = self.INT_MAX
            else:
                val = result

            # print(val)
            s.pop()
            s.add(x == val)

            return val

    def handle_COPY(self, last_operation, s, x, is_in_a_loop):
        log.info("Handle COPY: %s", last_operation)

        # Check the right value is a constant
        if last_operation.getInput(0).isConstant():
            return self.handle_Constant(last_operation.getInput(0), s, x)
        else:
            y = z3.BitVec(
                last_operation.getInput(0).toString(),
                self.bit_size,
            )
            s.add(x == y)
            return self.propgation(
                last_operation.getInput(0), last_operation, s, y, is_in_a_loop
            )

    def handle_CAST(self, last_operation, s, x, is_in_a_loop):
        log.info("Handle CAST: %s", last_operation)

        # Check the right value is a constant
        if last_operation.getInput(0).isConstant():
            return self.handle_Constant(last_operation.getInput(0), s, x)
        else:
            y = z3.BitVec(
                last_operation.getInput(0).toString(),
                self.bit_size,
            )
            s.add(x == y)
            return self.propgation(
                last_operation.getInput(0), last_operation, s, y, is_in_a_loop
            )

    def loop_check(self, last_operation):
        log.info("Checking %s in a loop or not", last_operation)

        block = last_operation.getParent()

        if block.getInSize() == 1 and block.getOutSize() == 1:
            if block.getIn(0) == block.getOut(0):
                log.debug("It it in a loop")
                return True

        return False

    def check_condition(self, input, original_op):
        log.info("Checking condition of %s", input)
        last_operation = input.getDef()
        log.info("Last operation is %s: ", last_operation)

        # Does this CBRANCH is loop initilizer
        is_loop = False

        block = original_op.getParent()
        if block.getInSize() == 2 and block.getOutSize() == 2:
            if block.getIn(1) == block.getOut(1):
                log.debug("loop initilizer")
            is_loop = True

        if is_loop:
            return True
        else:

            input0 = last_operation.getInput(0)
            input1 = last_operation.getInput(1)
            y = z3.BitVec(input0.toString(), self.bit_size)
            z = z3.BitVec(input1.toString(), self.bit_size)
            s = z3.Solver()

            if last_operation.getOpcode() == self.pcode.PcodeOp.INT_SLESS:
                log.info("It is a INT_SLESS, checking %s < %s", y, z)
                block = last_operation.getParent()
                value = self.propgation(
                    last_operation.getInput(0), last_operation, s, y, False
                )
                s.add(z == input1.getOffset())
                if s.check() == z3.sat:
                    result = s.model().eval(y < z)
                    log.debug("%s < %s is %s", y, z, result)
                    return result
            if last_operation.getOpcode() == self.pcode.PcodeOp.INT_LESS:
                log.info("It is a INT_LESS, checking %s < %s", y, z)
                block = last_operation.getParent()
                value = self.propgation(
                    last_operation.getInput(0), last_operation, s, y, False
                )
                s.add(z == input1.getOffset())
                if s.check() == z3.sat:
                    result = s.model().eval(z3.ULT(y, z))
                    log.debug("%s < %s is %s", y, z, result)
                    return result
            elif last_operation.getOpcode() == self.pcode.PcodeOp.INT_NOTEQUAL:
                log.info("It is a INT_NOTEQUAL, checking %s != %s", y, z)
                value = self.propgation(
                    last_operation.getInput(0), last_operation, s, y, False
                )
                if isinstance(value, Uncertain):
                    log.debug("The value can't be determained")
                    return self.uncertain
                else:
                    s.add(y != z, y == value, z == input1.getOffset())
                    if s.check() == z3.sat:
                        result = s.model().eval(y != z)
                        log.debug("%s != %s is %s", y, z, result)
                        return result
            elif last_operation.getOpcode() == self.pcode.PcodeOp.INT_EQUAL:
                log.info("It is a INT_EQUAL, checking %s = %s", y, z)
                value = self.propgation(
                    last_operation.getInput(0), last_operation, s, y, False
                )

                block = last_operation.getParent()

                if isinstance(value, Uncertain):
                    log.debug("The value can't be determained")
                    return self.uncertain
                else:
                    s.add(y == value, z == input1.getOffset())
                    if s.check() == z3.sat:
                        result = s.model().eval(y == z)
                        log.debug("%s == %s is %s", y, z, result)
                        if original_op.getParent() == block.getTrueOut():
                            log.debug("this branch is taken when condition is True ")
                            if result == True:
                                result = True
                        if original_op.getParent() == block.getFalseOut():
                            log.debug("this branch is taken when condition is False ")
                            if result == False:
                                result = True
                        return result

            else:
                log.error("Not implementated yet")

    # TODO: need more attentation.
    def handle_MULTIEQUAL(self, last_operation, s: z3.Solver, x, is_in_a_loop):
        log.info("handle MULTIEQUAL: %s", last_operation)
        if last_operation not in self.visited_operation:
            self.visited_operation.append(last_operation)
        else:
            log.debug("Terminted due to duplicate operation")
            return None

        log.debug("%s, %s", self.multiequals, last_operation.getSeqnum().toString())
        inputs = []
        if last_operation.getSeqnum().toString() in self.multiequals:
            inputs = self.multiequals[last_operation.getSeqnum().toString()]
        else:
            log.debug("Not just initialze one ")
            default_input = {"value": None, "postion": 0}
            for i in range(0, last_operation.getNumInputs()):
                inputs.append(default_input)

        log.debug(inputs)
        log.debug("Checking if need branch analysis...")

        # check if a input comes from a branch.
        value = None
        uncertain_values = []
        last_block = None

        postion = 0
        for i, input in enumerate(last_operation.getInputs()):
            # print(last_operation.getSeqnum(), last_operation)
            log.debug("Checking %s", input)

            if inputs != None:
                if inputs[i]["value"] != None:
                    log.debug("%s already has a value: %s", input, inputs[i]["value"])
                    continue
            else:
                log.debug("the_inputs is None")

            defination_of_input = input.getDef()
            if defination_of_input != None:
                block = defination_of_input.getParent()
                log.debug("The block of %s is %s", defination_of_input, block)
                iter = block.getIterator()
                if block.getInSize() == 1:

                    stop_op: PcodeOperation = None
                    iter = block.getIn(0).getIterator()
                    for op1 in iter:
                        stop_op = op1
                    if stop_op.getOpcode() == self.pcode.PcodeOp.CBRANCH:
                        log.debug("Found a cbranch: %s", stop_op)

                        result = self.check_condition(stop_op.getInput(1), stop_op)

                        if block == block.getIn(0).getTrueOut():
                            log.debug("this input is valid when condition is True ")
                            if result == True:
                                result = True
                        if block == block.getIn(0).getFalseOut():
                            log.debug("this input is valid when condition is False ")
                            if result == False:
                                result = True

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
                                            input, last_operation, s, x, is_in_a_loop
                                        )
                                        if result != None:
                                            log.info(
                                                "%s has a value %s, previous value will be replaced",
                                                input,
                                                result,
                                            )
                                            inputX = {
                                                "value": result,
                                                "postion": postion,
                                            }
                                            postion = postion + 1
                                            inputs[i] = inputX
                                            value = result

                                        s.pop()
                                    else:
                                        log.info("depth > 0, ignore this input")
                            else:
                                log.info(
                                    "last_block is None, %s is the first input", input
                                )
                                s.push()
                                result = self.propgation(
                                    input, last_operation, s, x, is_in_a_loop
                                )
                                inputX = {
                                    "value": result,
                                    "postion": postion,
                                }
                                inputs[i] = inputX
                                postion = postion + 1
                                value = result
                                if result != None:
                                    value = result
                                s.pop()
                                last_block = block

                            log.debug(value)

                        elif isinstance(result, Uncertain):
                            log.info(
                                "The condition is uncertain, need to perserve the value"
                            )
                            s.push()
                            result = self.propgation(
                                input, last_operation, s, x, is_in_a_loop
                            )
                            inputX = {
                                "value": result,
                                "postion": postion,
                            }
                            inputs[i] = inputX
                            postion = postion
                            value = result
                            if result != None:
                                value = result
                            if result != None:
                                uncertain_values.append(result)
                            s.pop()
                            last_block = block

                        else:
                            log.info(
                                "condition is False, no need for branch analysis, and this input can be ignore"
                            )
                    else:
                        log.info("input not from cbranch, do the normal analysis")
                        s.push()
                        result = self.propgation(
                            input, last_operation, s, x, is_in_a_loop
                        )
                        inputX = {
                            "value": result,
                            "postion": postion,
                        }
                        inputs[i] = inputX
                        postion = postion + 1
                        if result != None:
                            value = result
                        s.pop()
                        last_block = block

                else:
                    log.info(
                        "block has multiple or zero in blocks, it could be a entry block"
                    )
                    s.push()
                    result = self.propgation(input, last_operation, s, x, is_in_a_loop)
                    inputX = {
                        "value": result,
                        "postion": postion,
                    }
                    inputs[i] = inputX
                    postion = postion + 1
                    if result != None:
                        value = result
                    s.pop()
                last_block = block
            else:
                log.info("last operation is None")

            log.debug("After one round: %s", inputs)

        self.multiequals[last_operation.getSeqnum().toString()] = inputs
        log.debug(inputs)
        log.debug(self.multiequals)

        inputs.sort(key=lambda aaa: aaa["postion"])
        log.debug(inputs)

        if uncertain_values != []:

            if value in uncertain_values:
                log.info("value in uncertain_values, found the maxium")
            else:
                # TODO: Rewrite it when avaiable
                if value == None:
                    value = z3.BitVecVal(0, self.bit_size)

                log.info("value not in uncertain_values, found the maxium")

            # simple bubble sort
            for i in uncertain_values:
                if value.as_long() < i.as_long():
                    log.debug("transfer")
                    value = i

        else:
            log.info("Uncertain value is None")

        log.debug("Output of multiequal %s is %s", last_operation.getOutput(), value)
        if value != None:

            # print(x.size(), value.size())
            if x.size() != value.size():
                print("ext")
                s.add(z3.SignExt(value.size() - x.size(), x) == value)
                log.debug(value.as_signed_long())
            else:
                print("un ext")
                s.add(x == value)
                log.debug(value.as_signed_long())

            log.debug(value.as_signed_long())

            return value

    def handle_Unique(self, operation, s, x):
        log.error("Not implementated yet: %s", operation)

    def handle_CALL(
        self, operation, s, x, is_in_a_loop
    ) -> Uncertain | z3.BitVecNumRef | None:
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
            return self.uncertain
        if f.getName() == "_recv":
            log.debug(
                "call builtin function %s which return value can't be decided",
                f.getName(),
            )
            return self.uncertain
        if f.getName() == "_connect":
            log.debug(
                "call builtin function %s which return value can't be decided",
                f.getName(),
            )
            return self.uncertain
        if f.getName() == "_rand":
            log.debug(
                "call builtin function %s which return value can't be decided",
                f.getName(),
            )
            return self.uncertain

        if f.getName() == "strlen":
            print(f)
            print(operation.getInput(1))
            print(operation.getInput(1).getDef())

            input1 = self.propgation(
                operation.getInput(1), operation, s, x, is_in_a_loop
            )
            print(input1)
            return input1

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
                            return self.propgation(
                                op.getInput(1), op, s, x, is_in_a_loop
                            )
                    elif op.getNumInputs() == 1:
                        if op.getInput(0).isConstant():
                            log.info(
                                "The return don't have a return value, it may be a bad function call."
                            )
                        return self.uncertain
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

        value = z3.BitVecVal(value, self.bit_size)
        return value

    def handle_Register(self, input, s, x):
        log.info("handle Register")
        reg = self.func.getProgram().getRegister(input.getAddress(), input.getSize())

        value = z3.BitVecVal(reg.getBitLength(), self.bit_size)
        return value

    def handle_LOAD(self, operation, s, x, is_in_a_loop) -> Uncertain | None:
        log.info("handle LOAD: %s", operation)

        # Found store in current function
        # The most simple case, there is only one STORE in function
        # TODO: Make it more generic
        ops = self.high_function.getPcodeOps()
        for op in ops:
            if op.getOpcode() == self.pcode.PcodeOp.STORE:
                log.debug("Found the store in current function")
                return self.propgation(op.getInput(2), operation, s, x, is_in_a_loop)
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

                        return self.propgation(op.getInput(2), op, s, x, is_in_a_loop)

                log.debug("Not found a store, use found the indirect instead")
                ops = fffhigh.getPcodeOps()
                for op in ops:
                    # print(op.getSeqnum(), op)
                    if op.getOpcode() == self.pcode.PcodeOp.INDIRECT:
                        op1 = self.get_INDIRECT_operation(op)
                        for opppp in op1:
                            if opppp.getOpcode() == self.pcode.PcodeOp.COPY:
                                return self.handle_COPY(opppp, s, x, is_in_a_loop)
                log.info("Not found INDIRECT either, it could be any value")
                return self.uncertain

            elif ref.getReferenceType() == self.symbol.RefType.EXTERNAL_REF:
                log.info(
                    "This is a external reference, and the value can't be determained"
                )
                return self.uncertain
            else:
                log.error("Not cover yet")

    def handle_INT_ADD(
        self, current_operation, s, x, is_in_a_loop
    ) -> z3.BitVecNumRef | None:
        log.info("Handle INT_ADD: %s", current_operation)
        input0 = current_operation.getInput(0)
        input1 = current_operation.getInput(1)

        y = z3.BitVec(input0.toString(), input0.getSize() * 8)
        z = z3.BitVec(input1.toString(), input1.getSize() * 8)
        value = None
        if input0.isConstant():
            s.push()
            result = self.propgation(input1, input1.getDef(), s, z, is_in_a_loop)
            if result == None:
                val = None
            else:
                val = input0.getOffset() + result.as_signed_long()

            value = z3.BitVecVal(val, self.bit_size)
            s.pop()
            s.add(x == val)

        if input1.isConstant():
            s.push()
            result = self.propgation(input0, input0.getDef(), s, y, is_in_a_loop)
            print(result)
            if result == None:
                val = None
                s.pop()
                return None

            else:
                val = input1.getOffset() + result.as_signed_long()

                print(type(val))

                value = z3.BitVecVal(val, self.bit_size)

                s.pop()
                s.add(x == value)

                return value

    def handle_INT_MULT(
        self, current_operation, s, x, is_in_a_loop
    ) -> z3.BitVecNumRef | None:
        log.info("Handle INT_MULT: %s", current_operation)
        input0 = current_operation.getInput(0)
        input1 = current_operation.getInput(1)

        y = z3.BitVec(input0.toString(), input0.getSize() * 8)
        z = z3.BitVec(input1.toString(), input1.getSize() * 8)
        value = None
        if input0.isConstant():
            s.push()
            result = self.propgation(input1, input1.getDef(), s, z, is_in_a_loop)
            if result == None:
                val = None
            else:
                val = input0.getOffset() * result.as_signed_long()

            value = z3.BitVecVal(val, self.bit_size)
            s.pop()
            s.add(x == val)

        if input1.isConstant():
            s.push()
            result = self.propgation(input0, input0.getDef(), s, y, is_in_a_loop)
            # print(result)
            if result == None:
                val = None
                s.pop()
                return None

            else:
                val = input1.getOffset() * result.as_signed_long()

                # print(type(val))

                value = z3.BitVecVal(val, self.bit_size)

                s.pop()
                s.add(x == value)

                return value

    def loop_info(self, last_operation) -> dict[str, typing.Any] | None:
        block = last_operation.getParent().getIn(0)
        iter = block.getIterator()
        # print(block)

        for op in iter:
            # print(op)
            if op.getOpcode() == self.pcode.PcodeOp.CBRANCH:
                # print(op)
                # print(op.getInput(1))
                # print(op.getInput(1).getDef())
                # print(op.getInput(1).getDef().getInput(0).getDef())

                init = (
                    op.getInput(1)
                    .getDef()
                    .getInput(0)
                    .getDef()
                    .getInput(0)
                    .getDef()
                    .getInput(0)
                    .getOffset()
                )
                stride = (
                    op.getInput(1)
                    .getDef()
                    .getInput(0)
                    .getDef()
                    .getInput(1)
                    .getDef()
                    .getInput(1)
                    .getOffset()
                )

                info = {
                    "times": op.getInput(1).getOffset(),
                    "init": init,
                    "stride": stride,
                }
                log.debug("loop info: %s", info)

                return info

        log.warning("Can't retrive loop info")
        return None

    def handle_INT_AND(self, last_operation, s, x, is_in_a_loop) -> z3.BitVecNumRef:
        log.info("Handle INT_AND: %s", last_operation)
        input0 = last_operation.getInput(0)
        input1 = last_operation.getInput(1)

        y = z3.BitVec(input0.toString(), self.bit_size)

        s.push()
        input0 = self.propgation(input0, last_operation, s, y, is_in_a_loop)

        val = input0 & input1.getOffset()
        s.pop()

        s.add(x == val)

        return val

    def handle_INT_SREM(
        self, last_operation, s, x, is_in_a_loop
    ) -> z3.BitVecNumRef | None:
        log.info("Handle INT_SERM: %s", last_operation)
        input0 = last_operation.getInput(0)
        input1 = last_operation.getInput(1)

        y = z3.BitVec(input0.toString(), input0.getSize() * 8)
        z = z3.BitVec(input1.toString(), input1.getSize() * 8)
        val = None
        if input0.isConstant():
            s.push()
            result = self.propgation(input1, input1.getDef(), s, z, is_in_a_loop)
            if result == None:
                val = z3.BitVecVal(0, self.bit_size)
            else:
                val = input0.getOffset() % result.as_signed_long()

            s.pop()
            s.add(x == val)

        if input1.isConstant():
            s.push()
            result = self.propgation(input0, input0.getDef(), s, y, is_in_a_loop)
            if result == None:
                val = z3.BitVecVal(0, self.bit_size)
            else:
                val = result.as_signed_long() % input1.getOffset()

            s.pop()
            s.add(x == val)

        return val

    def handle_INT_SEXT(self, last_operation, s, x, is_in_a_loop):
        log.info("Handle INT_SEXT: %s", last_operation)
        # output = last_operation.getOutput()
        input0 = last_operation.getInput(0)

        # size = output.getSize() * 8
        input0.getSize()

        # x = z3.SignExt(size - x.size(), x)
        y = z3.BitVec(input0.toString(), input0.getSize() * 8)

        s.add(x == z3.SignExt(x.size() - y.size(), y))
        return self.propgation(input0, last_operation, s, y, is_in_a_loop)

    def handle_CALLIND(self, last_operation, s, x, is_in_a_loop):
        log.info("Handle CALLIND: %s", last_operation)
        # input0 = last_operation.getInput(0)
        input0 = last_operation.getInput(0)

        # Check the right value is a constant
        y = z3.BitVec(input0.toString(), input0.getSize() * 8)
        s.add(x == y)

        return self.propgation(input0, last_operation, s, y, is_in_a_loop)

    def handle_PTRSUB(self, last_operation, s, x, is_in_a_loop):
        log.info("Handle PTRSUB: %s", last_operation)
        input0 = last_operation.getInput(0)
        # input1 = last_operation.getInput(1)
        # print(input0.isInput())
        val = self.propgation(input0, last_operation, s, x, is_in_a_loop)
        # print(val)

        result = z3.BitVecVal(val.as_signed_long(), self.bit_size)
        return result

    def propgation(
        self, varnode, current_operation, s: z3.Solver, x, is_in_a_loop=False
    ) -> z3.BitVecNumRef | None:
        log.info("Propgation on %s", varnode)

        # loop
        if is_in_a_loop == None:
            is_in_a_loop = self.loop_check(current_operation)

        if is_in_a_loop:
            log.warning("It is in a loop, start loop summarization")
            info = self.loop_info(current_operation)
            # print(info)
            stride = info["stride"]
            times = info["times"]

            init_value_solver = z3.Solver()
            x = z3.BitVec(varnode.toString(), varnode.getSize() * 8)

            value = self.propgation(
                varnode, current_operation, init_value_solver, x, False
            )

            if not isinstance(value, int):
                value = value.as_long()

            if current_operation.getOpcode() == self.pcode.PcodeOp.INT_ADD:
                result = value + stride * times
                result = z3.BitVecVal(result, self.bit_size)
                return result
            else:
                log.error("Not handled yet")

        else:
            log.warning("It is not in a loop")

        last_operation = varnode.getDef()
        # strcpy etc.

        if last_operation != None:
            # iter = last_operation.getOutput().getDescendants()
            # for op in iter:
            #     if op.getOpcode() == self.pcode.PcodeOp.CALL:
            #         f = self.getFunctionAt(op.getInput(0).getAddress())
            #         print(f)

            log.debug(
                "Last operation is: %s %s", last_operation.getSeqnum(), last_operation
            )
            op_code = last_operation.getOpcode()
            r = None
            if op_code == self.pcode.PcodeOp.INDIRECT:
                r = self.handle_INDIRECT(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.COPY:
                r = self.handle_COPY(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.CAST:
                r = self.handle_CAST(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.MULTIEQUAL:
                r = self.handle_MULTIEQUAL(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.CALL:
                r = self.handle_CALL(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.LOAD:
                r = self.handle_LOAD(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.INT_ADD:
                r = self.handle_INT_ADD(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.INT_MULT:
                r = self.handle_INT_MULT(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.INT_AND:
                r = self.handle_INT_AND(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.INT_SREM:
                r = self.handle_INT_SREM(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.INT_SEXT:
                r = self.handle_INT_SEXT(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.CALLIND:
                r = self.handle_CALLIND(last_operation, s, x, is_in_a_loop)
            elif op_code == self.pcode.PcodeOp.PTRSUB:
                r = self.handle_PTRSUB(last_operation, s, x, is_in_a_loop)
            else:
                log.error("Not impLementated yet: %s", last_operation.getMnemonic())

            return r
        else:
            log.info("last_operation is None")
            if varnode.isAddress():
                return self.handle_Address(varnode, s, x)
            elif varnode.isRegister():
                return self.handle_Register(varnode, s, x)
            elif varnode.isConstant():
                return self.handle_Constant(varnode, s, x)
            log.error("last_operation is None, not implementated yet")
        return None

    def constant_propgation(
        self, varnode, operation
    ) -> Uncertain | z3.BitVecNumRef | None:
        # taking consider of all indirect operation
        self.multiequals.clear()
        self.visited_operation.clear()

        s = z3.Solver()
        x = z3.BitVec(varnode.toString(), self.bit_size)

        if varnode.getHigh() != None:
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

            for operation_temp in self.INDIRECT_list:
                ops = self.get_INDIRECT_operation(operation_temp)
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
        result = self.propgation(varnode, operation, s, x, None)
        self.multiequals.clear()
        self.visited_operation.clear()
        return result
