package net.sf.metacad.revenge.type;

import net.sf.metacad.revenge.expression.CodeExpression;

public enum PrimitiveTypes implements CodeType {
	BOOLEAN, VOID;

	@Override
	public CodeExpression implicitInitialValue() {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}
}
