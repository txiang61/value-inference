package value.solver;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import value.qual.BoolVal;
import value.qual.BottomVal;
import value.qual.IntRange;
import value.qual.StringVal;
import value.qual.UnknownVal;
import value.representation.TypeCheckValue;
import value.solver.encoder.ValueConstraintEncoderFactory;
import value.solver.representation.Z3InferenceValue;

public class ValueFormatTranslator extends Z3SmtFormatTranslator<Z3InferenceValue, TypeCheckValue> {

    public ValueFormatTranslator(Lattice lattice) {
        super(lattice);
    }

    @Override
    public AnnotationMirror decodeSolution(
            TypeCheckValue solution, ProcessingEnvironment processingEnv) {
        if (solution.isUnknownVal()) {
            AnnotationBuilder builder = new AnnotationBuilder(processingEnv, UnknownVal.class);
            return builder.build();
        }
        if (solution.isBottomVal()) {
            AnnotationBuilder builder = new AnnotationBuilder(processingEnv, BottomVal.class);
            return builder.build();
        }
        if (solution.isBoolVal()) {
            AnnotationBuilder builder = new AnnotationBuilder(processingEnv, BoolVal.class);
            return builder.build();
        }
        if (solution.isStringVal()) {
            AnnotationBuilder builder = new AnnotationBuilder(processingEnv, StringVal.class);
            return builder.build();
        }
        if (solution.isIntRange()) {
            AnnotationBuilder builder = new AnnotationBuilder(processingEnv, IntRange.class);
            builder.setValue("from", solution.getIntRangeLower());
            builder.setValue("to", solution.getIntRangeUpper());
            return builder.build();
        }

        return null;
    }

    @Override
    protected Z3InferenceValue serializeVarSlot(VariableSlot slot) {
        int slotID = slot.getId();
        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }
        Z3InferenceValue encodedSlot = Z3InferenceValue.makeVariableSlot(ctx, slotID);
        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    @Override
    protected Z3InferenceValue serializeConstantSlot(ConstantSlot slot) {
        int slotID = slot.getId();
        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        AnnotationMirror anno = slot.getValue();
        Z3InferenceValue encodedSlot = Z3InferenceValue.makeConstantSlot(ctx, slotID);
        if (AnnotationUtils.areSameByClass(anno, UnknownVal.class)) {
            encodedSlot.setUnknownVal(true);
        }
        if (AnnotationUtils.areSameByClass(anno, BottomVal.class)) {
            encodedSlot.setBottomVal(true);
        }
        if (AnnotationUtils.areSameByClass(anno, BoolVal.class)) {
            encodedSlot.setBoolVal(true);
        }
        if (AnnotationUtils.areSameByClass(anno, StringVal.class)) {
            encodedSlot.setStringVal(true);
        }
        if (AnnotationUtils.areSameByClass(anno, IntRange.class)) {
            encodedSlot.setIntRange(true);
            encodedSlot.setIntRangeLower(
                    AnnotationUtils.getElementValue(anno, "from", Long.class, true));
            encodedSlot.setIntRangeUpper(
                    AnnotationUtils.getElementValue(anno, "to", Long.class, true));
        }
        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    @Override
    public BoolExpr encodeSlotWellformnessConstraint(VariableSlot slot) {
        Z3InferenceValue value = slot.serialize(this);
        return ctx.mkAnd(
                // one hot
                ctx.mkXor(
                        ctx.mkXor(value.getUnknownVal(), value.getBottomVal()),
                        ctx.mkAnd(
                                ctx.mkXor(
                                        ctx.mkXor(value.getBoolVal(), value.getStringVal()),
                                        value.getIntRange()),
                                ctx.mkNot(
                                        ctx.mkAnd(
                                                value.getBoolVal(),
                                                value.getStringVal(),
                                                value.getIntRange())))),
                // min <= from <= to <= max
                ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(Long.MIN_VALUE)),
                ctx.mkLe(value.getIntRangeUpper(), ctx.mkInt(Long.MAX_VALUE)),
                ctx.mkLe(value.getIntRangeLower(), value.getIntRangeUpper()));
    }

    @Override
    public BoolExpr encodeSlotPreferenceConstraint(VariableSlot slot) {
        Z3InferenceValue value = slot.serialize(this);
        return ctx.mkAnd(ctx.mkNot(value.getUnknownVal()), ctx.mkNot(value.getBottomVal()));
    }

    @Override
    public Map<Integer, AnnotationMirror> decodeSolution(
            List<String> model, ProcessingEnvironment processingEnv) {

        Map<Integer, AnnotationMirror> result = new HashMap<>();
        Map<Integer, TypeCheckValue> solutionSlots = new HashMap<>();

        for (String line : model) {
            // each line is "varName value"
            String[] parts = line.split(" ");
            String value = parts[1];

            // Get slotID and component name
            int slotID;
            String component;
            int dashIndex = parts[0].indexOf("-");
            if (dashIndex < 0) {
                slotID = Integer.valueOf(parts[0]);
                component = null;
            } else {
                slotID = Integer.valueOf(parts[0].substring(0, dashIndex));
                component = parts[0].substring(dashIndex + 1);
            }

            // Create a fresh solution slot if needed in the map
            if (!solutionSlots.containsKey(slotID)) {
                solutionSlots.put(slotID, new TypeCheckValue());
            }

            TypeCheckValue z3Slot = solutionSlots.get(slotID);
            if (component.contentEquals("TOP")) {
                z3Slot.setUnknownVal(Boolean.parseBoolean(value));
            }
            if (component.contentEquals("BOTTOM")) {
                z3Slot.setBottomVal(Boolean.parseBoolean(value));
            }
            if (component.contentEquals("INTRANGE")) {
                z3Slot.setIntRange(Boolean.parseBoolean(value));
            }
            if (component.contentEquals("STRINGVAL")) {
                z3Slot.setStringVal(Boolean.parseBoolean(value));
            }
            if (component.contentEquals("BOOLVAL")) {
                z3Slot.setBoolVal(Boolean.parseBoolean(value));
            }
            if (component.contentEquals("from")) {
                z3Slot.setIntRangeLower(Long.parseLong(value));
            }
            if (component.contentEquals("to")) {
                z3Slot.setIntRangeUpper(Long.parseLong(value));
            }
        }

        for (Map.Entry<Integer, TypeCheckValue> entry : solutionSlots.entrySet()) {
            result.put(entry.getKey(), decodeSolution(entry.getValue(), processingEnv));
        }

        return result;
    }

    @Override
    protected ConstraintEncoderFactory<BoolExpr> createConstraintEncoderFactory() {
        return new ValueConstraintEncoderFactory(lattice, ctx, this);
    }
}