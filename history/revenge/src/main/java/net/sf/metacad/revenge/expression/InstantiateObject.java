package net.sf.metacad.revenge.expression;

import java.util.List;
import java.util.Map;
import java.util.SortedSet;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public class InstantiateObject extends ExpressionBase {

	private static final long serialVersionUID = -7227252566593422205L;

	String className;

	List<CodeExpression> constructorParameterValues;

	public InstantiateObject(String className, List<CodeExpression> constructorParameterValues) {
		super();
		this.className = className;
		this.constructorParameterValues = constructorParameterValues;
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		// ClassType classType = initialState.resolveClass(this.className);

		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public boolean isAbout(String variableName) {
		// TODO Auto-generated method stub
		// return false;
		throw new UnsupportedOperationException("not yet implemented");
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
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

}
