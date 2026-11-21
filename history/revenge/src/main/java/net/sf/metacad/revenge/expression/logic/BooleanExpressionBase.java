package net.sf.metacad.revenge.expression.logic;

import net.sf.metacad.revenge.expression.ExpressionBase;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.PrimitiveTypes;

public abstract class BooleanExpressionBase extends ExpressionBase implements BooleanExpression {
	private static final long serialVersionUID = 1L;

	@Override
	public BooleanExpression negate() {
		return NotExpression.create(this);
	}

	@Override
	public CodeType type() {
		return PrimitiveTypes.BOOLEAN;
	}

}
