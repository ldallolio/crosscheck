package net.sf.metacad.revenge.expression.arithmetic;

import java.util.Map;
import java.util.SortedSet;

import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.ExpressionBase;
import net.sf.metacad.revenge.expression.UnaryExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

/**
 * @author Luca Dall'Olio
 *
 */
public class PostIncrementExpression extends ExpressionBase implements IntegerExpression, UnaryExpression {

	private static final long serialVersionUID = 2445991236924279865L;
	public final ArithmeticVariableReference variableReference;

	public PostIncrementExpression(ArithmeticVariableReference variableReference) {
		super();
		this.variableReference = variableReference;
	}

	@Override
	public boolean isAbout(String variableName) {
		return variableReference.isAbout(variableName);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		return variableReference.affectedVariables();
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CodeType type() {
		return variableReference.type();
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException {
		CodeExpression initialValue = initialState.variableValue(variableReference.name).cloneExpression();
		initialState.assignVariable(variableReference.name, BinaryIntegerExpression
				.create(BinaryArithmeticOperator.PLUS, initialValue, new IntegerValueExpression(1)));
		initialState.setLeftValue(initialValue);
		return initialState;
	}

	@Override
	public String toString() {
		return variableReference.localName + "++";
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public boolean contains(CodeExpression search) {
		return (equals(search) || variableReference.contains(search));
	}

}
