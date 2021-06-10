package value.solver.encoder;

import checkers.inference.model.ComparisonConstraint.ComparisonOperationKind;
import checkers.inference.model.ComparisonVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ComparisonConstraintEncoder;
import checkers.inference.solver.backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import org.checkerframework.javacutil.BugInCF;
import value.representation.TypeCheckValue;
import value.solver.representation.Z3InferenceValue;

public class ValueComparisonConstraintEncoder extends ValueAbstractConstraintEncoder
        implements ComparisonConstraintEncoder<BoolExpr> {

    public ValueComparisonConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceValue, TypeCheckValue> formatTranslator) {
        super(lattice, ctx, formatTranslator);
    }

    protected BoolExpr encode(
            ComparisonOperationKind operation, Slot left, Slot right, Slot result) {
        Z3InferenceValue l = left.serialize(z3SmtFormatTranslator);
        Z3InferenceValue r = right.serialize(z3SmtFormatTranslator);
        Z3InferenceValue res = result.serialize(z3SmtFormatTranslator);

        BoolExpr encoding;

        switch (operation) {
            case EQUAL_TO:
                encoding =
                        ctx.mkOr(
                                ctx.mkAnd(
                                        valueZ3SmtEncoderUtils.subtype(ctx, l, r),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, l)),
                                ctx.mkAnd(
                                        valueZ3SmtEncoderUtils.subtype(ctx, r, l),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, r)),
                                ctx.mkAnd(
                                        ctx.mkOr(l.getIntRange(), l.getUnknownVal()),
                                        r.getIntRange(),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        l.getIntRangeLower(),
                                                                        r.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        l.getIntRangeLower(),
                                                                        r.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                res.getIntRange(),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        l.getIntRangeUpper(),
                                                                        r.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        l.getIntRangeUpper(),
                                                                        r.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                res.getIntRange(),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        r.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        r.getIntRangeLower(),
                                                                        l.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                res.getIntRange(),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        r.getIntRangeLower()))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                res.getIntRange(),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        r.getIntRangeUpper()))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        l.getIntRangeUpper(),
                                                                        r.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeLower())),
                                                        res.getBottomVal()))));
                break;
            case NOT_EQUAL_TO:
                encoding =
                        ctx.mkOr(
                                ctx.mkAnd(
                                        ctx.mkOr(l.getBottomVal(), ctx.mkNot(r.getIntRange())),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, l)),
                                ctx.mkAnd(
                                        ctx.mkOr(l.getIntRange(), l.getUnknownVal()),
                                        r.getIntRange(),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkNot(
                                                                ctx.mkEq(
                                                                        r.getIntRangeLower(),
                                                                        r.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        l.getIntRangeLower(),
                                                                        l.getIntRangeUpper()),
                                                                ctx.mkEq(
                                                                        r.getIntRangeLower(),
                                                                        r.getIntRangeUpper()),
                                                                ctx.mkNot(
                                                                        ctx.mkEq(
                                                                                l
                                                                                        .getIntRangeLower(),
                                                                                r
                                                                                        .getIntRangeLower()))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        l.getIntRangeLower(),
                                                                        l.getIntRangeUpper()),
                                                                ctx.mkEq(
                                                                        r.getIntRangeLower(),
                                                                        r.getIntRangeUpper()),
                                                                ctx.mkEq(
                                                                        l.getIntRangeLower(),
                                                                        r.getIntRangeLower())),
                                                        res.getBottomVal()),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        r.getIntRangeLower(),
                                                                        r.getIntRangeUpper()),
                                                                ctx.mkEq(
                                                                        l.getIntRangeLower(),
                                                                        r.getIntRangeLower()),
                                                                ctx.mkNot(
                                                                        ctx.mkEq(
                                                                                l
                                                                                        .getIntRangeLower(),
                                                                                l
                                                                                        .getIntRangeUpper()))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        ctx.mkAdd(
                                                                                ctx.mkInt(1),
                                                                                l
                                                                                        .getIntRangeLower())),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        r.getIntRangeLower(),
                                                                        r.getIntRangeUpper()),
                                                                ctx.mkEq(
                                                                        l.getIntRangeUpper(),
                                                                        r.getIntRangeLower()),
                                                                ctx.mkNot(
                                                                        ctx.mkEq(
                                                                                l
                                                                                        .getIntRangeLower(),
                                                                                l
                                                                                        .getIntRangeUpper()))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        ctx.mkSub(
                                                                                l
                                                                                        .getIntRangeUpper(),
                                                                                ctx.mkInt(1))),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))))));
                break;
            case GREATER_THAN:
                encoding =
                        ctx.mkOr(
                                ctx.mkAnd(
                                        ctx.mkOr(l.getBottomVal(), ctx.mkNot(r.getIntRange())),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, l)),
                                ctx.mkAnd(
                                        ctx.mkOr(l.getIntRange(), l.getUnknownVal()),
                                        r.getIntRange(),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkGt(
                                                                l.getIntRangeLower(),
                                                                r.getIntRangeLower()),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        r.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkLt(
                                                                        r.getIntRangeLower(),
                                                                        l.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        ctx.mkAdd(
                                                                                r
                                                                                        .getIntRangeLower(),
                                                                                ctx.mkInt(1))),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkLe(
                                                                l.getIntRangeUpper(),
                                                                r.getIntRangeLower()),
                                                        res.getBottomVal()))));
                break;
            case GREATER_THAN_EQUAL:
                encoding =
                        ctx.mkOr(
                                ctx.mkAnd(
                                        ctx.mkOr(l.getBottomVal(), ctx.mkNot(r.getIntRange())),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, l)),
                                ctx.mkAnd(
                                        ctx.mkOr(l.getIntRange(), l.getUnknownVal()),
                                        r.getIntRange(),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkGe(
                                                                l.getIntRangeLower(),
                                                                r.getIntRangeLower()),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        r.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        r.getIntRangeLower(),
                                                                        l.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        r.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkLt(
                                                                l.getIntRangeUpper(),
                                                                r.getIntRangeLower()),
                                                        res.getBottomVal()))));
                break;
            case LESS_THAN:
                encoding =
                        ctx.mkOr(
                                ctx.mkAnd(
                                        ctx.mkOr(l.getBottomVal(), ctx.mkNot(r.getIntRange())),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, l)),
                                ctx.mkAnd(
                                        ctx.mkOr(l.getIntRange(), l.getUnknownVal()),
                                        r.getIntRange(),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkLt(
                                                                l.getIntRangeUpper(),
                                                                r.getIntRangeUpper()),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        ctx.mkSub(
                                                                                r
                                                                                        .getIntRangeUpper(),
                                                                                ctx.mkInt(1))),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkGe(
                                                                l.getIntRangeLower(),
                                                                r.getIntRangeUpper()),
                                                        res.getBottomVal()))));
                break;
            case LESS_THAN_EQUAL:
                encoding =
                        ctx.mkOr(
                                ctx.mkAnd(
                                        ctx.mkOr(l.getBottomVal(), ctx.mkNot(r.getIntRange())),
                                        valueZ3SmtEncoderUtils.equality(ctx, res, l)),
                                ctx.mkAnd(
                                        ctx.mkOr(l.getIntRange(), l.getUnknownVal()),
                                        r.getIntRange(),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkLe(
                                                                l.getIntRangeUpper(),
                                                                r.getIntRangeUpper()),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        l.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGe(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkLe(
                                                                        r.getIntRangeUpper(),
                                                                        l.getIntRangeUpper())),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        l.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        r.getIntRangeUpper()),
                                                                valueZ3SmtEncoderUtils.isIntRange(
                                                                        ctx, res))),
                                                ctx.mkImplies(
                                                        ctx.mkGt(
                                                                l.getIntRangeLower(),
                                                                r.getIntRangeUpper()),
                                                        res.getBottomVal()))));
                break;
            default:
                throw new BugInCF(
                        "Attempting to encode an unsupported comparison operation: "
                                + operation
                                + " left: "
                                + left
                                + " right: "
                                + right);
        }
        return encoding;
    }

    @Override
    public BoolExpr encodeVariable_Variable(
            ComparisonOperationKind operation,
            VariableSlot left,
            VariableSlot right,
            ComparisonVariableSlot result) {
        return encode(operation, left, right, result);
    }

    @Override
    public BoolExpr encodeVariable_Constant(
            ComparisonOperationKind operation,
            VariableSlot left,
            ConstantSlot right,
            ComparisonVariableSlot result) {
        return encode(operation, left, right, result);
    }

    @Override
    public BoolExpr encodeConstant_Variable(
            ComparisonOperationKind operation,
            ConstantSlot left,
            VariableSlot right,
            ComparisonVariableSlot result) {
        return ctx.mkTrue();
    }

    @Override
    public BoolExpr encodeConstant_Constant(
            ComparisonOperationKind operation,
            ConstantSlot left,
            ConstantSlot right,
            ComparisonVariableSlot result) {
        return ctx.mkTrue();
    }
}
