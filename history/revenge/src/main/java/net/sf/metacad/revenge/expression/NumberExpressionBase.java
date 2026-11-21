package net.sf.metacad.revenge.expression;

import java.util.SortedSet;
import java.util.TreeSet;

/**
 * Seems that the actual value will not matter in SOS, is this true? mmh looks like in while loops it will matter...
 * 
 * @author ldallolio
 * 
 */
public abstract class NumberExpressionBase extends ExpressionBase implements ConstantExpression {

	private static final long serialVersionUID = -6773157323091781453L;

	@Override
	final public boolean isAbout(String variableName) {
		// constant is never about a variable
		return false;
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		return new TreeSet<>();
	}
}
