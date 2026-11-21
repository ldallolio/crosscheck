package net.sf.metacad.revenge.expression;

import java.io.Serializable;
import java.util.Map;
import java.util.SortedSet;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.StateTransition;
import net.sf.metacad.revenge.type.CodeType;

public interface CodeExpression extends Serializable, Cloneable, StateTransition {
	boolean isAbout(String variableName);

	SortedSet<VariableReference> affectedVariables();

	void accept(CodeExpressionVisitor visitor);

	CodeExpression replace(CodeExpression search, CodeExpression replace);

	boolean contains(CodeExpression search);

	void repeat(IntegerExpression times, CodeExpressionVisitor visitor, Map<String, CodeExpression> initialValues);

	CodeExpression cloneExpression();

	CodeType type();
}