package value.solver.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import value.representation.TypeCheckValue;
import value.solver.representation.Z3InferenceValue;

public class ValueComparableConstraintEncoder extends ValueAbstractConstraintEncoder
        implements ComparableConstraintEncoder<BoolExpr> {

    public ValueComparableConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceValue, TypeCheckValue> formatTranslator) {
        super(lattice, ctx, formatTranslator);
    }

    protected BoolExpr encode(Slot fst, Slot snd) {
        Z3InferenceValue first = fst.serialize(z3SmtFormatTranslator);
        Z3InferenceValue second = snd.serialize(z3SmtFormatTranslator);

        return ctx.mkOr(
                valueZ3SmtEncoderUtils.subtype(ctx, first, second),
                valueZ3SmtEncoderUtils.subtype(ctx, second, first));
    }

    @Override
    public BoolExpr encodeVariable_Variable(VariableSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public BoolExpr encodeVariable_Constant(VariableSlot fst, ConstantSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public BoolExpr encodeConstant_Variable(ConstantSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }
}
