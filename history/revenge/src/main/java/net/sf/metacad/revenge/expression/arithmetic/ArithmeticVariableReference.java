package net.sf.metacad.revenge.expression.arithmetic;

import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.type.CodeType;

public class ArithmeticVariableReference extends VariableReference implements ArithmeticExpression {

	private static final long serialVersionUID = -1960843855216797820L;

	public ArithmeticVariableReference(String name, String localName, CodeType type) {
		super(name, localName, type);
	}

	public ArithmeticVariableReference(String name, CodeType type) {
		super(name, type);
	}

}
