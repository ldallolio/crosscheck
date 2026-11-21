package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.type.CodeType;

public class ObjectExpression extends ExpressionBase {

	public ObjectExpression() {
		objectState.setCreatorDescription(new ToStringBuilder(this).toString());
	}

	private static final long serialVersionUID = 2996407673569168445L;

	ProgramState objectState = new ProgramState();

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

	@Override
	public CodeState evaluate(CodeState initialState) {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

}
