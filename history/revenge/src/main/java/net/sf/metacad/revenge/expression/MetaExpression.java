package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public enum MetaExpression implements CodeExpression, Cloneable {

	NULL_EXPRESSION, DEFINED_BUT_NOT_INITIALIZED_VARIABLE, NO_LEFT_VALUE, NOT_DEFINED_VARIABLE, NO_RETURN_VALUE, NO_RECURSION;

	@Override
	public CodeExpression cloneExpression() {
		try {
			return (CodeExpression) clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}

	@Override
	public boolean isAbout(String variableName) {
		return false;
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		return new TreeSet<>();
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		// Should have a corresponding visitor method, so that it can put
		// something on the stack and the pop() it
		// Another solution, only during "binding", avoid all push and pop, but
		// it could break complex expression visiting
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		throw new IllegalStateException("Should not try to project : [" + name() + "]");
	}

	@Override
	public CodeType type() {
		// Probably create a MetaType ?;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		initialState.setLeftValue(this);
		return initialState;
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return this;
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		return equals(search);
	}

}
