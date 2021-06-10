package value.solver;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.SourceVariableSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.backend.z3smt.encoder.Z3SmtSoftConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import value.qual.BottomVal;
import value.qual.IntRange;
import value.qual.PolyVal;
import value.qual.UnknownVal;
import value.representation.TypeCheckValue;
import value.solver.encoder.ValueConstraintEncoderFactory;
import value.solver.encoder.ValueZ3SmtSoftConstraintEncoder;
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
        //        if (solution.isBoolVal()) {
        //            AnnotationBuilder builder = new AnnotationBuilder(processingEnv,
        // BoolVal.class);
        //            return builder.build();
        //        }
        //        if (solution.isStringVal()) {
        //            AnnotationBuilder builder = new AnnotationBuilder(processingEnv,
        // StringVal.class);
        //            return builder.build();
        //        }
        if (solution.isIntRange()) {
            long from = solution.getIntRangeLower();
            long to = solution.getIntRangeUpper();
            if (from == Long.MIN_VALUE && to == Long.MAX_VALUE) {
                AnnotationBuilder builder = new AnnotationBuilder(processingEnv, UnknownVal.class);
                return builder.build();
            } else {
                AnnotationBuilder builder = new AnnotationBuilder(processingEnv, IntRange.class);
                builder.setValue("from", solution.getIntRangeLower());
                builder.setValue("to", solution.getIntRangeUpper());
                return builder.build();
            }
        }

        return null;
    }

    @Override
    protected Z3InferenceValue serializeVariableSlot(VariableSlot slot) {
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
        // TODO: temp hack: treat poly as unknownval
        if (AnnotationUtils.areSameByClass(anno, PolyVal.class)) {
            encodedSlot.setUnknownVal(true);
        }
        if (AnnotationUtils.areSameByClass(anno, UnknownVal.class)) {
            encodedSlot.setUnknownVal(true);
            encodedSlot.setIntRangeUpper(Long.MAX_VALUE);
            encodedSlot.setIntRangeLower(Long.MIN_VALUE);
        }
        if (AnnotationUtils.areSameByClass(anno, BottomVal.class)) {
            encodedSlot.setBottomVal(true);
        }
        //        if (AnnotationUtils.areSameByClass(anno, BoolVal.class)) {
        //            encodedSlot.setBoolVal(true);
        //        }
        //        if (AnnotationUtils.areSameByClass(anno, StringVal.class)) {
        //            encodedSlot.setStringVal(true);
        //        }
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
    public BoolExpr encodeSlotWellformednessConstraint(VariableSlot slot) {
        Z3InferenceValue value = slot.serialize(this);
        BoolExpr range =
                ctx.mkAnd(
                        ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(Long.MIN_VALUE)),
                        ctx.mkLe(value.getIntRangeUpper(), ctx.mkInt(Long.MAX_VALUE)));
        if (slot instanceof SourceVariableSlot) {
            TypeMirror type = ((SourceVariableSlot) slot).getUnderlyingType();
            if (type == null) {
                return ctx.mkAnd(
                        // one hot
                        ctx.mkAnd(
                                ctx.mkXor(
                                        ctx.mkXor(value.getUnknownVal(), value.getBottomVal()),
                                        value.getIntRange()),
                                ctx.mkNot(
                                        ctx.mkAnd(
                                                value.getUnknownVal(),
                                                value.getBottomVal(),
                                                value.getIntRange()))),
                        // min <= from <= to <= max
                        range,
                        ctx.mkLe(value.getIntRangeLower(), value.getIntRangeUpper()));
                //            	return ctx.mkAnd(
                //                        // one hot
                //                        ctx.mkXor(
                //                                ctx.mkXor(value.getUnknownVal(),
                // value.getBottomVal()),
                //                                ctx.mkAnd(
                //                                        ctx.mkXor(
                //                                                ctx.mkXor(value.getBoolVal(),
                // value.getStringVal()),
                //                                                value.getIntRange()),
                //                                        ctx.mkNot(
                //                                                ctx.mkAnd(
                //                                                        value.getBoolVal(),
                //                                                        value.getStringVal(),
                //                                                        value.getIntRange())))),
                //                        // min <= from <= to <= max
                //                        range,
                //                        ctx.mkLe(value.getIntRangeLower(),
                // value.getIntRangeUpper()));
            }
            if (type.getKind() == TypeKind.BYTE || type.toString().equals("java.lang.Byte")) {
                range =
                        ctx.mkAnd(
                                value.getIntRange(),
                                ctx.mkNot(value.getUnknownVal()),
                                //                                ctx.mkNot(value.getBoolVal()),
                                //                                ctx.mkNot(value.getStringVal()),
                                ctx.mkNot(value.getBottomVal()),
                                ctx.mkOr(
                                        ctx.mkAnd(
                                                ctx.mkGe(
                                                        value.getIntRangeLower(),
                                                        ctx.mkInt(Byte.MIN_VALUE)),
                                                ctx.mkLe(
                                                        value.getIntRangeUpper(),
                                                        ctx.mkInt(Byte.MAX_VALUE))),
                                        ctx.mkAnd(
                                                ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(0)),
                                                ctx.mkLe(
                                                        value.getIntRangeUpper(),
                                                        ctx.mkInt(Byte.MAX_VALUE * 2 + 1))),
                                        ctx.mkAnd(
                                                ctx.mkGe(
                                                        value.getIntRangeLower(),
                                                        ctx.mkInt(Byte.MIN_VALUE)),
                                                ctx.mkLe(
                                                        value.getIntRangeUpper(),
                                                        ctx.mkInt(Byte.MAX_VALUE * 2 + 1)))));
            }
            if (type.getKind() == TypeKind.SHORT || type.toString().equals("java.lang.Short")) {
                range =
                        ctx.mkAnd(
                                value.getIntRange(),
                                ctx.mkNot(value.getUnknownVal()),
                                //                                ctx.mkNot(value.getBoolVal()),
                                //                                ctx.mkNot(value.getStringVal()),
                                ctx.mkNot(value.getBottomVal()),
                                ctx.mkOr(
                                        ctx.mkAnd(
                                                value.getIntRange(),
                                                ctx.mkGe(
                                                        value.getIntRangeLower(),
                                                        ctx.mkInt(Short.MIN_VALUE)),
                                                ctx.mkLe(
                                                        value.getIntRangeUpper(),
                                                        ctx.mkInt(Short.MAX_VALUE))),
                                        ctx.mkAnd(
                                                value.getIntRange(),
                                                ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(0)),
                                                ctx.mkLe(
                                                        value.getIntRangeUpper(),
                                                        ctx.mkInt(Short.MAX_VALUE * 2 + 1))),
                                        ctx.mkAnd(
                                                value.getIntRange(),
                                                ctx.mkGe(
                                                        value.getIntRangeLower(),
                                                        ctx.mkInt(Short.MIN_VALUE)),
                                                ctx.mkLe(
                                                        value.getIntRangeUpper(),
                                                        ctx.mkInt(Short.MAX_VALUE * 2 + 1)))));
            }
            if (type.getKind() == TypeKind.CHAR || type.toString().equals("java.lang.Character")) {
                range =
                        ctx.mkAnd(
                                value.getIntRange(),
                                ctx.mkNot(value.getUnknownVal()),
                                //                                ctx.mkNot(value.getBoolVal()),
                                //                                ctx.mkNot(value.getStringVal()),
                                ctx.mkNot(value.getBottomVal()),
                                ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(Character.MIN_VALUE)),
                                ctx.mkLe(value.getIntRangeUpper(), ctx.mkInt(Character.MAX_VALUE)));
            }
            if (type.getKind() == TypeKind.INT || type.toString().equals("java.lang.Integer")) {
                range =
                        ctx.mkAnd(
                                value.getIntRange(),
                                ctx.mkNot(value.getUnknownVal()),
                                //                                ctx.mkNot(value.getBoolVal()),
                                //                                ctx.mkNot(value.getStringVal()),
                                ctx.mkNot(value.getBottomVal()),
                                ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(Integer.MIN_VALUE)),
                                ctx.mkLe(value.getIntRangeUpper(), ctx.mkInt(Integer.MAX_VALUE)));
            }
            if (type.getKind() == TypeKind.LONG || type.toString().equals("java.lang.Long")) {
                range =
                        ctx.mkAnd(
                                ctx.mkOr(value.getIntRange(), value.getUnknownVal()),
                                //                                ctx.mkNot(value.getBoolVal()),
                                //                                ctx.mkNot(value.getStringVal()),
                                ctx.mkNot(value.getBottomVal()),
                                ctx.mkGe(value.getIntRangeLower(), ctx.mkInt(Long.MIN_VALUE)),
                                ctx.mkLe(value.getIntRangeUpper(), ctx.mkInt(Long.MAX_VALUE)));
            }
        }
        BoolExpr unknownVal =
                ctx.mkAnd(
                        value.getUnknownVal(),
                        ctx.mkEq(value.getIntRangeLower(), ctx.mkInt(Long.MIN_VALUE)),
                        ctx.mkEq(value.getIntRangeUpper(), ctx.mkInt(Long.MAX_VALUE)));
        return ctx.mkAnd(
                // one hot
                ctx.mkAnd(
                        ctx.mkXor(ctx.mkXor(unknownVal, value.getBottomVal()), value.getIntRange()),
                        ctx.mkNot(
                                ctx.mkAnd(unknownVal, value.getBottomVal(), value.getIntRange()))),
                // min <= from <= to <= max
                range,
                ctx.mkLe(value.getIntRangeLower(), value.getIntRangeUpper()));
        //        return ctx.mkAnd(
        //                // one hot
        //                ctx.mkXor(
        //                        ctx.mkXor(value.getUnknownVal(), value.getBottomVal()),
        //                        ctx.mkAnd(
        //                                ctx.mkXor(
        //                                        ctx.mkXor(value.getBoolVal(),
        // value.getStringVal()),
        //                                        value.getIntRange()),
        //                                ctx.mkNot(
        //                                        ctx.mkAnd(
        //                                                value.getBoolVal(),
        //                                                value.getStringVal(),
        //                                                value.getIntRange())))),
        //                // min <= from <= to <= max
        //                range,
        //                ctx.mkLe(value.getIntRangeLower(), value.getIntRangeUpper()));
    }

    @Override
    public BoolExpr encodeSlotPreferenceConstraint(VariableSlot slot) {
        Z3InferenceValue value = slot.serialize(this);
        if (slot instanceof SourceVariableSlot) {
            TypeMirror type = ((SourceVariableSlot) slot).getUnderlyingType();
            if (type == null) {
                return value.getBottomVal();
            }
            //            if (type.toString().equals("java.lang.String")) {
            //                return value.getStringVal();
            //            }
            //            if (type.getKind() == TypeKind.BOOLEAN ||
            // type.toString().equals("java.lang.Boolean")) {
            //                return value.getBoolVal();
            //            }
            if (type.getKind() == TypeKind.BYTE || type.toString().equals("java.lang.Byte")) {
                return ctx.mkAnd(
                        value.getIntRange(),
                        ctx.mkEq(value.getIntRangeLower(), ctx.mkInt(Byte.MIN_VALUE)),
                        ctx.mkEq(value.getIntRangeUpper(), ctx.mkInt(Byte.MAX_VALUE)));
            }
            if (type.getKind() == TypeKind.SHORT || type.toString().equals("java.lang.Short")) {
                return ctx.mkAnd(
                        value.getIntRange(),
                        ctx.mkEq(value.getIntRangeLower(), ctx.mkInt(Short.MIN_VALUE)),
                        ctx.mkEq(value.getIntRangeUpper(), ctx.mkInt(Short.MAX_VALUE)));
            }
            if (type.getKind() == TypeKind.CHAR || type.toString().equals("java.lang.Character")) {
                return ctx.mkAnd(
                        value.getIntRange(),
                        ctx.mkEq(value.getIntRangeLower(), ctx.mkInt(Character.MIN_VALUE)),
                        ctx.mkEq(value.getIntRangeUpper(), ctx.mkInt(Character.MAX_VALUE)));
            }
            if (type.getKind() == TypeKind.INT || type.toString().equals("java.lang.Integer")) {
                return ctx.mkAnd(
                        value.getIntRange(),
                        ctx.mkEq(value.getIntRangeLower(), ctx.mkInt(Integer.MIN_VALUE)),
                        ctx.mkEq(value.getIntRangeUpper(), ctx.mkInt(Integer.MAX_VALUE)));
            }
            if (type.getKind() == TypeKind.LONG || type.toString().equals("java.lang.Long")) {
                return ctx.mkAnd(
                        value.getIntRange(),
                        ctx.mkEq(value.getIntRangeLower(), ctx.mkInt(Long.MIN_VALUE)),
                        ctx.mkEq(value.getIntRangeUpper(), ctx.mkInt(Long.MAX_VALUE)));
            }
        }

        return ctx.mkNot(value.getIntRange());
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
            //            if (component.contentEquals("STRINGVAL")) {
            //                z3Slot.setStringVal(Boolean.parseBoolean(value));
            //            }
            //            if (component.contentEquals("BOOLVAL")) {
            //                z3Slot.setBoolVal(Boolean.parseBoolean(value));
            //            }
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

    @Override
    protected Z3SmtSoftConstraintEncoder<Z3InferenceValue, TypeCheckValue>
            createSoftConstraintEncoder() {
        return new ValueZ3SmtSoftConstraintEncoder(lattice, ctx, this);
    }
}
