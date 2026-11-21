package net.sf.metacad.revenge.type;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.RationalValueExpression;

public enum NumericType implements CodeType {
	INT(new IntegerValueExpression(0)), RATIONAL(RationalValueExpression.create(0, 1));

	private final CodeExpression implicitInitialValue;

	private NumericType(CodeExpression implicitInitialValue) {
		this.implicitInitialValue = implicitInitialValue;
	}

	@Override
	public CodeExpression implicitInitialValue() {
		return implicitInitialValue;
	}
}
