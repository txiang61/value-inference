package value.solver.encoder;

import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.SourceVariableSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ArithmeticConstraintEncoder;
import checkers.inference.solver.backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntNum;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import org.checkerframework.javacutil.BugInCF;
import value.representation.TypeCheckValue;
import value.solver.representation.Z3InferenceValue;

public class ValueArithmeticConstraintEncoder extends ValueAbstractConstraintEncoder
        implements ArithmeticConstraintEncoder<BoolExpr> {

    public ValueArithmeticConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceValue, TypeCheckValue> formatTranslator) {
        super(lattice, ctx, formatTranslator);
    }

    protected BoolExpr encode(
            ArithmeticOperationKind operation,
            Slot leftOperand,
            Slot rightOperand,
            ArithmeticVariableSlot result) {
        Z3InferenceValue left = leftOperand.serialize(z3SmtFormatTranslator);
        Z3InferenceValue right = rightOperand.serialize(z3SmtFormatTranslator);
        Z3InferenceValue res = result.serialize(z3SmtFormatTranslator);

        BoolExpr encoding =
                ctx.mkAnd(
                        //                        ctx.mkNot(res.getBoolVal()),
                        //                        ctx.mkImplies(
                        //                                ctx.mkAnd(left.getIntRange(),
                        // right.getStringVal()),
                        //                                res.getStringVal()),
                        //                        ctx.mkImplies(
                        //                                ctx.mkAnd(left.getStringVal(),
                        // right.getIntRange()),
                        //                                res.getStringVal()),
                        //                        ctx.mkImplies(
                        //                                ctx.mkAnd(left.getStringVal(),
                        // right.getStringVal()),
                        //                                res.getStringVal()),
                        ctx.mkImplies(
                                ctx.mkAnd(left.getBottomVal(), right.getBottomVal()),
                                res.getBottomVal()),
                        ctx.mkImplies(left.getUnknownVal(), res.getUnknownVal()),
                        ctx.mkImplies(right.getUnknownVal(), res.getUnknownVal())
                        //                        ctx.mkImplies(
                        //                                ctx.mkAnd(left.getIntRange(),
                        // right.getIntRange()),
                        //                                ctx.mkNot(res.getBottomVal()))
                        );

        // Unless variable type is long, all arithmetic operations in Java are widened to int first,
        IntNum maxRange = ctx.mkInt(Integer.MAX_VALUE);
        IntNum minRange = ctx.mkInt(Integer.MIN_VALUE);
        if (leftOperand instanceof SourceVariableSlot) {
            TypeMirror type = ((SourceVariableSlot) leftOperand).getUnderlyingType();
            if (type.getKind() == TypeKind.LONG) {
                maxRange = ctx.mkInt(Long.MAX_VALUE);
                minRange = ctx.mkInt(Long.MIN_VALUE);
            }
        } else if (rightOperand instanceof SourceVariableSlot) {
            TypeMirror type = ((SourceVariableSlot) rightOperand).getUnderlyingType();
            if (type.getKind() == TypeKind.LONG) {
                maxRange = ctx.mkInt(Long.MAX_VALUE);
                minRange = ctx.mkInt(Long.MIN_VALUE);
            }
        }

        switch (operation) {
            case PLUS:
                ArithExpr plus_up = ctx.mkAdd(left.getIntRangeUpper(), right.getIntRangeUpper());
                ArithExpr plus_lo = ctx.mkAdd(left.getIntRangeLower(), right.getIntRangeLower());
                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkAnd(
                                                        ctx.mkEq(res.getIntRangeUpper(), plus_up),
                                                        ctx.mkEq(res.getIntRangeLower(), plus_lo),
                                                        ctx.mkLe(plus_up, maxRange),
                                                        ctx.mkGe(plus_lo, minRange)),
                                                ctx.mkAnd(
                                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                                        ctx.mkEq(res.getIntRangeUpper(), maxRange),
                                                        ctx.mkOr(
                                                                ctx.mkGt(plus_up, maxRange),
                                                                ctx.mkLt(plus_lo, minRange))))),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case MINUS:
                ArithExpr minus_lo = ctx.mkSub(left.getIntRangeLower(), right.getIntRangeUpper());
                ArithExpr minus_up = ctx.mkSub(left.getIntRangeUpper(), right.getIntRangeLower());
                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkAnd(
                                                        ctx.mkEq(res.getIntRangeUpper(), minus_up),
                                                        ctx.mkEq(res.getIntRangeLower(), minus_lo),
                                                        ctx.mkLe(minus_up, maxRange),
                                                        ctx.mkGe(minus_lo, minRange)),
                                                ctx.mkAnd(
                                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                                        ctx.mkEq(res.getIntRangeUpper(), maxRange),
                                                        ctx.mkOr(
                                                                ctx.mkGt(minus_up, maxRange),
                                                                ctx.mkLt(minus_lo, minRange))))),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case MULTIPLY:
                ArithExpr mul1 = ctx.mkMul(left.getIntRangeUpper(), right.getIntRangeUpper());
                ArithExpr mul2 = ctx.mkMul(left.getIntRangeLower(), right.getIntRangeLower());
                ArithExpr mul3 = ctx.mkMul(left.getIntRangeUpper(), right.getIntRangeLower());
                ArithExpr mul4 = ctx.mkMul(left.getIntRangeLower(), right.getIntRangeUpper());

                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkAnd(
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkGe(mul1, mul2),
                                                                        ctx.mkGe(mul1, mul3),
                                                                        ctx.mkGe(mul1, mul4)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        mul1)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkGe(mul2, mul1),
                                                                        ctx.mkGe(mul2, mul3),
                                                                        ctx.mkGe(mul2, mul4)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        mul2)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkGe(mul3, mul1),
                                                                        ctx.mkGe(mul3, mul2),
                                                                        ctx.mkGe(mul3, mul4)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        mul3)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkGe(mul4, mul1),
                                                                        ctx.mkGe(mul4, mul2),
                                                                        ctx.mkGe(mul4, mul3)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        mul4)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkLe(mul1, mul2),
                                                                        ctx.mkLe(mul1, mul3),
                                                                        ctx.mkLe(mul1, mul4)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        mul1)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkLe(mul2, mul1),
                                                                        ctx.mkLe(mul2, mul3),
                                                                        ctx.mkLe(mul2, mul4)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        mul2)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkLe(mul3, mul1),
                                                                        ctx.mkLe(mul3, mul2),
                                                                        ctx.mkLe(mul3, mul4)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        mul3)),
                                                        ctx.mkImplies(
                                                                ctx.mkAnd(
                                                                        ctx.mkLe(mul4, mul1),
                                                                        ctx.mkLe(mul4, mul2),
                                                                        ctx.mkLe(mul4, mul3)),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        mul4)),
                                                        ctx.mkLt(mul1, maxRange),
                                                        ctx.mkLt(mul2, maxRange),
                                                        ctx.mkLt(mul3, maxRange),
                                                        ctx.mkLt(mul4, maxRange),
                                                        ctx.mkGt(mul1, minRange),
                                                        ctx.mkGt(mul2, minRange),
                                                        ctx.mkGt(mul3, minRange),
                                                        ctx.mkGt(mul4, minRange)),
                                                ctx.mkAnd(
                                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                                        ctx.mkEq(res.getIntRangeUpper(), maxRange),
                                                        ctx.mkOr(
                                                                ctx.mkGt(mul1, maxRange),
                                                                ctx.mkGt(mul2, maxRange),
                                                                ctx.mkGt(mul3, maxRange),
                                                                ctx.mkGt(mul4, maxRange),
                                                                ctx.mkLt(mul1, minRange),
                                                                ctx.mkLt(mul2, minRange),
                                                                ctx.mkLt(mul3, minRange),
                                                                ctx.mkLt(mul4, minRange))))),
                                ctx.mkNot(res.getIntRange())));
            case DIVIDE:
                ArithExpr div_upup = ctx.mkDiv(left.getIntRangeUpper(), right.getIntRangeUpper());
                ArithExpr div_uplo = ctx.mkDiv(left.getIntRangeUpper(), right.getIntRangeLower());
                ArithExpr div_lolo = ctx.mkDiv(left.getIntRangeLower(), right.getIntRangeLower());
                ArithExpr div_loup = ctx.mkDiv(left.getIntRangeLower(), right.getIntRangeUpper());
                ArithExpr div_neglo = ctx.mkMul(left.getIntRangeLower(), ctx.mkInt(-1));
                ArithExpr div_negup = ctx.mkMul(left.getIntRangeUpper(), ctx.mkInt(-1));

                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkAnd(
                                                // pos / pos
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkGt(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_uplo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_loup))),
                                                // pos / neg
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_lolo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_upup))),
                                                // neg / pos
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkLt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkGt(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_upup),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_lolo))),
                                                // neg / neg
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkLt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_loup),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_uplo))),
                                                // pos / unknown
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkGt(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_negup),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        left.getIntRangeUpper()))),
                                                // neg / unknown
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkLt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkGt(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        left.getIntRangeLower()),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_neglo))),
                                                // unknown / pos
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkGt(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_lolo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_uplo))),
                                                // unknown / neg
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_upup),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_loup))),
                                                // unknown / unknown
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkGt(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkImplies(
                                                                        ctx.mkLt(
                                                                                left
                                                                                        .getIntRangeLower(),
                                                                                div_negup),
                                                                        ctx.mkEq(
                                                                                res
                                                                                        .getIntRangeLower(),
                                                                                left
                                                                                        .getIntRangeLower())),
                                                                ctx.mkImplies(
                                                                        ctx.mkGt(
                                                                                left
                                                                                        .getIntRangeLower(),
                                                                                div_negup),
                                                                        ctx.mkEq(
                                                                                res
                                                                                        .getIntRangeLower(),
                                                                                div_negup)),
                                                                ctx.mkImplies(
                                                                        ctx.mkLt(
                                                                                div_neglo,
                                                                                left
                                                                                        .getIntRangeLower()),
                                                                        ctx.mkEq(
                                                                                res
                                                                                        .getIntRangeUpper(),
                                                                                left
                                                                                        .getIntRangeLower())),
                                                                ctx.mkImplies(
                                                                        ctx.mkGt(
                                                                                div_neglo,
                                                                                left
                                                                                        .getIntRangeLower()),
                                                                        ctx.mkEq(
                                                                                res
                                                                                        .getIntRangeUpper(),
                                                                                div_neglo)))),
                                                // any / 0
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        right.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkEq(
                                                                        right.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        maxRange),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        minRange))))),
                                ctx.mkNot(res.getIntRange())));
            case REMAINDER:
                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkImplies(
                                                ctx.mkGe(right.getIntRangeLower(), ctx.mkInt(0)),
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                res.getIntRangeLower(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkEq(
                                                                res.getIntRangeUpper(),
                                                                right.getIntRangeUpper()))),
                                        ctx.mkImplies(
                                                ctx.mkLe(right.getIntRangeUpper(), ctx.mkInt(0)),
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                res.getIntRangeUpper(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkEq(
                                                                res.getIntRangeLower(),
                                                                right.getIntRangeLower()))),
                                        ctx.mkImplies(
                                                ctx.mkAnd(
                                                        ctx.mkLe(
                                                                right.getIntRangeLower(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkGe(
                                                                right.getIntRangeUpper(),
                                                                ctx.mkInt(0))),
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                res.getIntRangeLower(),
                                                                right.getIntRangeLower()),
                                                        ctx.mkEq(
                                                                res.getIntRangeUpper(),
                                                                right.getIntRangeUpper())))),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case LEFT_SHIFT:
                // The value of n << s is n left-shifted s bit positions. Equivalent to
                // multiplication by 2 to the power s.

                ArithExpr mul_upup =
                        ctx.mkMul(
                                left.getIntRangeUpper(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeUpper()));
                ArithExpr mul_lolo =
                        ctx.mkMul(
                                left.getIntRangeLower(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeLower()));
                ArithExpr mul_uplo =
                        ctx.mkMul(
                                left.getIntRangeUpper(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeLower()));
                ArithExpr mul_loup =
                        ctx.mkMul(
                                left.getIntRangeLower(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeUpper()));

                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkLe(right.getIntRangeLower(), ctx.mkInt(0)),
                                                ctx.mkGe(right.getIntRangeUpper(), ctx.mkInt(31))),
                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                        ctx.mkEq(res.getIntRangeUpper(), maxRange)),
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkGe(right.getIntRangeLower(), ctx.mkInt(0)),
                                        ctx.mkLe(right.getIntRangeUpper(), ctx.mkInt(31)),
                                        ctx.mkAnd(
                                                ctx.mkImplies(
                                                        ctx.mkGt(
                                                                left.getIntRangeUpper(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkEq(res.getIntRangeUpper(), mul_upup)),
                                                ctx.mkImplies(
                                                        ctx.mkLt(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkEq(res.getIntRangeLower(), mul_loup)),
                                                ctx.mkImplies(
                                                        ctx.mkGt(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkEq(res.getIntRangeLower(), mul_lolo)),
                                                ctx.mkImplies(
                                                        ctx.mkLt(
                                                                left.getIntRangeUpper(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkEq(
                                                                res.getIntRangeUpper(),
                                                                mul_uplo)))),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case RIGHT_SHIFT:
                div_upup =
                        ctx.mkDiv(
                                left.getIntRangeUpper(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeUpper()));
                div_uplo =
                        ctx.mkDiv(
                                left.getIntRangeUpper(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeLower()));
                div_lolo =
                        ctx.mkDiv(
                                left.getIntRangeLower(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeLower()));
                div_loup =
                        ctx.mkDiv(
                                left.getIntRangeLower(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeUpper()));

                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkLe(right.getIntRangeLower(), ctx.mkInt(0)),
                                                ctx.mkGe(right.getIntRangeUpper(), ctx.mkInt(31))),
                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                        ctx.mkEq(res.getIntRangeUpper(), maxRange)),
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkGe(right.getIntRangeLower(), ctx.mkInt(0)),
                                        ctx.mkLe(right.getIntRangeUpper(), ctx.mkInt(31)),
                                        ctx.mkAnd(
                                                // pos / pos
                                                ctx.mkImplies(
                                                        ctx.mkGt(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_uplo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_loup))),
                                                // neg / pos
                                                ctx.mkImplies(
                                                        ctx.mkLt(
                                                                left.getIntRangeUpper(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_upup),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_lolo))),
                                                // unknown / pos
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_lolo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_uplo))))),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case UNSIGNED_RIGHT_SHIFT:
                div_upup =
                        ctx.mkDiv(
                                left.getIntRangeUpper(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeUpper()));
                div_uplo =
                        ctx.mkDiv(
                                left.getIntRangeUpper(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeLower()));
                div_lolo =
                        ctx.mkDiv(
                                left.getIntRangeLower(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeLower()));
                div_loup =
                        ctx.mkDiv(
                                left.getIntRangeLower(),
                                ctx.mkPower(ctx.mkInt(2), right.getIntRangeUpper()));

                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkLe(right.getIntRangeLower(), ctx.mkInt(0)),
                                                ctx.mkGe(right.getIntRangeUpper(), ctx.mkInt(31))),
                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                        ctx.mkEq(res.getIntRangeUpper(), maxRange)),
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkGe(right.getIntRangeLower(), ctx.mkInt(0)),
                                        ctx.mkLe(right.getIntRangeUpper(), ctx.mkInt(31)),
                                        ctx.mkAnd(
                                                // pos / pos
                                                ctx.mkImplies(
                                                        ctx.mkGt(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_uplo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_loup))),
                                                // neg / pos
                                                ctx.mkImplies(
                                                        ctx.mkLt(
                                                                left.getIntRangeUpper(),
                                                                ctx.mkInt(0)),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_upup),
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_lolo))),
                                                // unknown / pos
                                                ctx.mkImplies(
                                                        ctx.mkAnd(
                                                                ctx.mkGt(
                                                                        left.getIntRangeUpper(),
                                                                        ctx.mkInt(0)),
                                                                ctx.mkLt(
                                                                        left.getIntRangeLower(),
                                                                        ctx.mkInt(0))),
                                                        ctx.mkAnd(
                                                                ctx.mkEq(
                                                                        res.getIntRangeLower(),
                                                                        div_lolo),
                                                                ctx.mkEq(
                                                                        res.getIntRangeUpper(),
                                                                        div_uplo))))),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case XOR:
                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                        ctx.mkEq(res.getIntRangeUpper(), maxRange)),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case AND:
                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkOr(
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                left.getIntRangeLower(),
                                                                left.getIntRangeUpper()),
                                                        ctx.mkGe(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0))),
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                right.getIntRangeLower(),
                                                                right.getIntRangeUpper()),
                                                        ctx.mkGe(
                                                                right.getIntRangeLower(),
                                                                ctx.mkInt(0)))),
                                        ctx.mkImplies(
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                left.getIntRangeLower(),
                                                                left.getIntRangeUpper()),
                                                        ctx.mkGe(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0))),
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                res.getIntRangeUpper(),
                                                                left.getIntRangeLower()),
                                                        ctx.mkEq(
                                                                res.getIntRangeLower(),
                                                                ctx.mkInt(0)))),
                                        ctx.mkImplies(
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                right.getIntRangeLower(),
                                                                right.getIntRangeUpper()),
                                                        ctx.mkGe(
                                                                right.getIntRangeLower(),
                                                                ctx.mkInt(0))),
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                res.getIntRangeUpper(),
                                                                right.getIntRangeLower()),
                                                        ctx.mkEq(
                                                                res.getIntRangeLower(),
                                                                ctx.mkInt(0))))),
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkNot(
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                left.getIntRangeLower(),
                                                                left.getIntRangeUpper()),
                                                        ctx.mkGe(
                                                                left.getIntRangeLower(),
                                                                ctx.mkInt(0)))),
                                        ctx.mkNot(
                                                ctx.mkAnd(
                                                        ctx.mkEq(
                                                                right.getIntRangeLower(),
                                                                right.getIntRangeUpper()),
                                                        ctx.mkGe(
                                                                right.getIntRangeLower(),
                                                                ctx.mkInt(0)))),
                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                        ctx.mkEq(res.getIntRangeUpper(), maxRange)),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            case OR:
                return ctx.mkAnd(
                        encoding,
                        ctx.mkOr(
                                ctx.mkAnd(
                                        left.getIntRange(),
                                        right.getIntRange(),
                                        res.getIntRange(),
                                        ctx.mkEq(res.getIntRangeLower(), minRange),
                                        ctx.mkEq(res.getIntRangeUpper(), maxRange)),
                                ctx.mkAnd(
                                        ctx.mkOr(
                                                ctx.mkNot(left.getIntRange()),
                                                ctx.mkNot(right.getIntRange())),
                                        ctx.mkNot(res.getIntRange()))));
            default:
                throw new BugInCF(
                        "Attempting to encode an unsupported arithmetic operation: "
                                + operation
                                + " leftOperand: "
                                + leftOperand
                                + " rightOperand: "
                                + rightOperand
                                + " result: "
                                + result);
        }
    }

    @Override
    public BoolExpr encodeVariable_Variable(
            ArithmeticOperationKind operation,
            VariableSlot leftOperand,
            VariableSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public BoolExpr encodeVariable_Constant(
            ArithmeticOperationKind operation,
            VariableSlot leftOperand,
            ConstantSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public BoolExpr encodeConstant_Variable(
            ArithmeticOperationKind operation,
            ConstantSlot leftOperand,
            VariableSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public BoolExpr encodeConstant_Constant(
            ArithmeticOperationKind operation,
            ConstantSlot leftOperand,
            ConstantSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }
}
