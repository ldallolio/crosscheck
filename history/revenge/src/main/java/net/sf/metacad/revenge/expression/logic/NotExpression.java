package net.sf.metacad.revenge.expression.logic;

import java.util.Map;
import java.util.SortedSet;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.UnaryExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;

/**
 * @author Luca Dall'Olio
 *
 */
public class NotExpression extends BooleanExpressionBase implements BooleanExpression, UnaryExpression {

	private static final long serialVersionUID = -2267239020447419775L;
	public final CodeExpression rightSide;

	private NotExpression(CodeExpression rightSide) {
		super();
		this.rightSide = rightSide;
	}

	static public BooleanExpression create(BooleanExpression rightSide) {

		if (rightSide == null) {
			throw new IllegalArgumentException("Right side not valid : [" + rightSide + "]");
		}

		if (BooleanValueExpression.TRUE.equals(rightSide)) {
			return BooleanValueExpression.FALSE;
		}

		if (BooleanValueExpression.FALSE.equals(rightSide)) {
			return BooleanValueExpression.TRUE;
		}

		if (rightSide instanceof NotExpression) {
			// Involution Law
			return (BooleanExpression) ((NotExpression) rightSide).rightSide;
		}

		if (rightSide instanceof ComparisonExpression) {
			ComparisonExpression comparisonExpression = (ComparisonExpression) rightSide;
			BooleanExpression result;
			switch (comparisonExpression.operator) {
			case EQUAL:
				result = ComparisonExpression.create(ComparisonOperator.NOTEQUAL, comparisonExpression.leftSide,
						comparisonExpression.rightSide);
				break;
			case GREATEREQUALTHAN:
				result = ComparisonExpression.create(ComparisonOperator.LESSERTHAN, comparisonExpression.leftSide,
						comparisonExpression.rightSide);
				break;
			case LESSEREQUALTHAN:
				result = ComparisonExpression.create(ComparisonOperator.GREATERTHAN, comparisonExpression.leftSide,
						comparisonExpression.rightSide);
				break;
			case GREATERTHAN:
				result = ComparisonExpression.create(ComparisonOperator.LESSEREQUALTHAN, comparisonExpression.leftSide,
						comparisonExpression.rightSide);
				break;
			case LESSERTHAN:
				result = ComparisonExpression.create(ComparisonOperator.GREATEREQUALTHAN, comparisonExpression.leftSide,
						comparisonExpression.rightSide);
				break;
			case NOTEQUAL:
				result = ComparisonExpression.create(ComparisonOperator.EQUAL, comparisonExpression.leftSide,
						comparisonExpression.rightSide);
				break;
			default:
				throw new UnsupportedOperationException(
						"Operator : [" + comparisonExpression.operator + "] not yet handled.");
			}
			return result;
		} else if (rightSide instanceof BinaryBooleanExpression) {
			BinaryBooleanExpression binaryExpression = (BinaryBooleanExpression) rightSide;
			BooleanExpression result;
			switch (binaryExpression.operator) {
			case AND:
				// De Morgan !a&&b == !a || !b
				result = BinaryBooleanExpression.create(BinaryBooleanOperator.OR,
						NotExpression.create((BooleanExpression) binaryExpression.getLeftSide()),
						NotExpression.create((BooleanExpression) binaryExpression.getRightSide()));
				break;
			case OR:
				// De Morgan !a||b == !a && !b
				result = BinaryBooleanExpression.create(BinaryBooleanOperator.AND,
						NotExpression.create((BooleanExpression) binaryExpression.getLeftSide()),
						NotExpression.create((BooleanExpression) binaryExpression.getRightSide()));
				break;
			default:
				throw new UnsupportedOperationException(
						"Operator : [" + binaryExpression.operator + "] not yet handled.");
			}
			return result;

		}

		return new NotExpression(rightSide);
	}

	@Override
	public boolean isAbout(String variableName) {
		return rightSide.isAbout(variableName);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		return rightSide.affectedVariables();
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.negate(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState rightSideState = rightSide.evaluate(initialState);
		rightSideState.setLeftValue(NotExpression.create((BooleanExpression) rightSideState.getLeftValue()));
		return rightSideState;
	}

	@Override
	public String toString() {
		return "NOT(" + rightSide.toString() + ")";
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return NotExpression.create((BooleanExpression) rightSide.replace(search, replace));
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		return (equals(search) || rightSide.contains(search));
	}

}
