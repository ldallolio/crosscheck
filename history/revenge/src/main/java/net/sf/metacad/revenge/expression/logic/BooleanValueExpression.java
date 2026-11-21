package net.sf.metacad.revenge.expression.logic;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.ConstantExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.PrimitiveTypes;

public enum BooleanValueExpression implements BooleanExpression, CodeExpression, ConstantExpression {

	TRUE, FALSE;

	static final BooleanValueExpression create(boolean value) {
		if (value) {
			return TRUE;
		} else {
			return FALSE;
		}
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		return new TreeSet<>();
	}

	@Override
	public CodeExpression cloneExpression() {
		return this;
	}

	@Override
	public boolean isAbout(String variableName) {
		return false;
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeType type() {
		return PrimitiveTypes.BOOLEAN;
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		initialState.setLeftValue(this);
		return initialState;
	}

	public boolean booleanValue() {
		return equals(TRUE);
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

	@Override
	public BooleanExpression negate() {
		return NotExpression.create(this);
	}

}