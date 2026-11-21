package net.sf.metacad.revenge.state;

import java.io.Serializable;

import net.sf.metacad.revenge.expression.CodeExpression;

public interface CodeState
		extends Cloneable, Serializable, VariableCodeState, FunctionCodeState, ClassCodeState, CycleCodeState {
	void recordFact(CodeExpression fact);

	void retreatFact(CodeExpression fact);

	CodeExpression getLeftValue();

	void setLeftValue(CodeExpression leftValue);

	CodeState cloneState();

	void setWrappingState(WrappingState wrappingState);

	void setCreatorDescription(String creatorDescription);

}