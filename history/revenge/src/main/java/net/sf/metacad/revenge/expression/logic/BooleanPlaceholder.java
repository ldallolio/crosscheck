package net.sf.metacad.revenge.expression.logic;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.PlaceholderExpression;
import net.sf.metacad.revenge.expression.PlaceholderExpressionBase;

public class BooleanPlaceholder extends PlaceholderExpressionBase implements BooleanExpression, PlaceholderExpression {

	private static final long serialVersionUID = -1L;

	public BooleanPlaceholder(String placeholderName, String placeholderLocalName, String variableName,
			CodeExpression variableCurrentValue, String creatorDescription) {
		super(placeholderName, placeholderLocalName, variableName, variableCurrentValue, creatorDescription);
	}

	public BooleanPlaceholder(String placeholderName) {
		super(placeholderName);
	}

	@Override
	public BooleanExpression negate() {
		return NotExpression.create(this);
	}

}
