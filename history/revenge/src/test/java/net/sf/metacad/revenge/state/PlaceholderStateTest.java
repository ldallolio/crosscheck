package net.sf.metacad.revenge.state;

import static org.junit.Assert.assertNotNull;

import java.util.Map;

import org.junit.Test;

import bsh.JavaParser;
import net.sf.metacad.revenge.constraint.ConstraintSolver;
import net.sf.metacad.revenge.constraint.RepeatProjector;
import net.sf.metacad.revenge.constraint.SymbolicConstraintVisitor;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.arithmetic.ArithmeticVariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.statement.Assignment;
import net.sf.metacad.revenge.type.NumericType;

public class PlaceholderStateTest {

	private transient ConstraintSolver visitor = new SymbolicConstraintVisitor();

	@Test
	public void testExternalVariable() throws Exception {
		// When adding eternal layer of while, placeholder value is protected,
		// but it is then simplified : is a protected placeholder value so
		// similar to placeholder reference?
		// Possibly adding a versioning to the placeholder to prevent equal
		// simplification, or (better) split the concept of placeholder
		// reference and placeholder value ?
		ProgramState programState = new ProgramState();
		programState.defineVariable(new VariableDefinition("j", NumericType.INT, new IntegerValueExpression(9)));
		// PlaceholderState externalState = new PlaceholderState(programState
		// .cloneState());
		CodeState externalState = programState.cloneState();
		PlaceholderState placeholderState = new PlaceholderState(externalState);
		StateTransition whileClause = ComparisonExpression.create(ComparisonOperator.NOTEQUAL,
				placeholderState.variableValue("j"), new IntegerValueExpression(13));
		CodeState whileClauseState = whileClause.evaluate(placeholderState);
		placeholderState.setPlaceholding(false);
		CodeState whileClauseStateCloned = whileClauseState.cloneState();
		placeholderState.setPlaceholding(true);
		StateTransition whileBody = new Assignment(new ArithmeticVariableReference("j", "j", NumericType.INT),
				BinaryIntegerExpression.create(BinaryArithmeticOperator.PLUS, placeholderState.variableValue("j"),
						new IntegerValueExpression(1)));
		CodeState whileBodyState = whileBody.evaluate(whileClauseState);
		assertNotNull(whileBodyState);
		placeholderState.setPlaceholding(false);
		BooleanExpression repeatExpression = (BooleanExpression) whileClauseStateCloned.getLeftValue();
		Map<String, CodeExpression> finalVariables = RepeatProjector.solveRepeatProblem(whileClauseStateCloned,
				placeholderState, repeatExpression, visitor, null, null);
		assertNotNull(finalVariables);
		System.out.println(repeatExpression);
	}

	@Test
	public void testPostincrement() throws Exception {
		CodeState initialState = JavaParser.evaluate("int i = 9;");
		PlaceholderState placeholderState = new PlaceholderState(initialState);
		CodeExpression postincr = (CodeExpression) JavaParser.parse("i++;", placeholderState);
		postincr.evaluate(placeholderState);
		// placeholderState.setPlaceholding(false);
		System.out.println(placeholderState.getLeftValue());
	}
}
