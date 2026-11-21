package net.sf.metacad.revenge.expression.arithmetic;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.PlaceholderExpression;
import net.sf.metacad.revenge.expression.PlaceholderExpressionBase;

public class IntegerPlaceholder extends PlaceholderExpressionBase implements IntegerExpression, PlaceholderExpression {

	private static final long serialVersionUID = -875954665147919897L;

	public IntegerPlaceholder(String placeholderName, String placeholderLocalName, String variableName,
			CodeExpression variableCurrentValue, String creatorDescription) {
		super(placeholderName, placeholderLocalName, variableName, variableCurrentValue, creatorDescription);
	}

	public IntegerPlaceholder(String placeholderName) {
		super(placeholderName);
	}
}
