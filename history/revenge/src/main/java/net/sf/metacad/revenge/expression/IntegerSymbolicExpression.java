package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;

public class IntegerSymbolicExpression extends ExpressionBase
		implements CodeExpression, IntegerExpression, SymbolicExpression {

	private static final long serialVersionUID = -1604811034617301920L;

	public final String name;
	public final String localName;
	public final CodeExpression value;

	public IntegerSymbolicExpression(String name, String localName, CodeExpression value) {
		this.name = name;
		this.localName = localName;
		this.value = value;

	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public String getLocalName() {
		return localName;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
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
		visitor.useSymbol(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		visitor.useSymbol(this);
	}

	@Override
	public CodeExpression cloneExpression() {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeType type() {
		return NumericType.INT;
	}

	@Override
	public String toString() {
		return localName;
	}

}
