package net.sf.metacad.revenge.statement;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import bsh.JavaParser;
import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.IntegerSymbolicExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.state.StateTransition;
import net.sf.metacad.revenge.type.NumericType;

public class WhileStatementTest {

	@Test
	public void testEvaluate() throws Exception {

		String code = "int i = 7; while (i != 13) i = i + 1;";

		CodeState finalState = JavaParser.evaluate(code);
		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testEvaluatePostincrement() throws Exception {

		String code = "int i = 7; while (i != 13) i++;";

		CodeState finalState = JavaParser.evaluate(code);
		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testEvaluateLessthan() throws Exception {

		String code = "int i = 7; while (i < 13) i = i + 1;";

		CodeState finalState = JavaParser.evaluate(code);
		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testEvaluateSymbolic() throws Exception {
		VariableDefinition variableDefinition = new VariableDefinition("i", NumericType.INT,
				new IntegerSymbolicExpression("random", "random", null));
		ProgramState programState = new ProgramState();
		programState.defineVariable(variableDefinition);

		try {
			CodeState finalState = JavaParser.evaluate("while (i != 13) i = i + 1;", programState);
			assertTrue(false);
		} catch (CannotSolveException e) {
			assertTrue(true);
			// TODO should somehow detect the conditions under which while-cycle and recursion "never exiting"
			// or "never entering"
			// condition, for example when symbols are presents :
			// int i = System.in.read(); while (i != 13) i = i + 1;
			// In this example, if initial System.in.read()==14 it will never exit
			// the cycle, but final value hypothesis (i == NOT(i_0_final!=13)) will
			// think it will certainly exit (wrong)
		}
	}

	@Test
	public void testPostincrementInClause() throws Exception {

		CodeState finalState = JavaParser.evaluate("int i = 0; while (i++ < 13) {};");

		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	// @Test
	public void testPaperSample() throws Exception {

		VariableDefinition variableDefinition = new VariableDefinition("n", NumericType.INT,
				new IntegerSymbolicExpression("random", "random", null));
		ProgramState programState = new ProgramState();
		programState.defineVariable(variableDefinition);

		CodeState finalState = JavaParser
				.evaluate("int i = 0; int x = 0; int y = 0; while (i++ < n) {x = y + 2;y = x + 3;}", programState);

		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testEvaluateWithIf() throws Exception {

		StateTransition whileStatement = JavaParser.parse("int i = 7; while (i != 13) if (i != 13) i = i + 1;");

		ProgramState programState = new ProgramState();

		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testBlock() throws Exception {
		StateTransition whileStatement = JavaParser.parse("int i = 0;int x;while (i != 1) {x = i; i = i + 1;}");
		CodeState finalState = whileStatement.evaluate(new ProgramState());
		assertEquals(1, ((IntegerValueExpression) finalState.variableValue("i")).value);
		assertEquals(0, ((IntegerValueExpression) finalState.variableValue("x")).value);
	}

	@Test
	public void testZeroIterations() throws Exception {
		StateTransition whileStatement = JavaParser.parse("int i = 0;while (i != 0) i = i + 1;");
		ProgramState programState = new ProgramState();
		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(0, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testOneIterationStepsIndependent() throws Exception {
		StateTransition whileStatement = JavaParser.parse("int i = 0;while (i == 0) i = 1;");
		ProgramState programState = new ProgramState();
		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(1, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testInfiniteIterations() throws Exception {
		StateTransition whileStatement = JavaParser.parse("int i = 0;while (i != 1) i = 0;");
		try {
			whileStatement.evaluate(new ProgramState());
			assertTrue(false);
		} catch (UnFeasibleException e) {
			assertTrue(true);
		}
	}

	/*
	 * @Test public void testInfiniteIterations2() throws Exception { StateTransition whileStatement = interpreter
	 * .parse("while (1 != 0) {};"); try { whileStatement.evaluate(new ProgramState()); assertTrue(false); } catch
	 * (UnFeasibleException e) { assertTrue(true); } }
	 */

	@Test
	public void testLinearCoupling() throws Exception {

		StateTransition whileStatement = JavaParser
				.parse("int i = -42; int j = 1; while ((i + j) < 10) {i = j + 2; j = i + 3;}");

		ProgramState programState = new ProgramState();

		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(8, ((IntegerValueExpression) finalState.variableValue("i")).value);
		assertEquals(11, ((IntegerValueExpression) finalState.variableValue("j")).value);
	}

	@Test
	public void testLinearCouplingInBody() throws Exception {

		StateTransition whileStatement = JavaParser
				.parse("int i = 1; int x = 1; int y = 1; while (i != 10) {i = i + 1; x = y + 2; y = x + 3;}");

		ProgramState programState = new ProgramState();

		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(10, ((IntegerValueExpression) finalState.variableValue("i")).value);
		assertEquals(43, ((IntegerValueExpression) finalState.variableValue("x")).value);
		assertEquals(46, ((IntegerValueExpression) finalState.variableValue("y")).value);
	}

	@Test
	public void testPlusTimesCoupling() throws Exception {

		StateTransition whileStatement = JavaParser.parse("int i = 0; while (i < 10) {i = i + 2; i = i * 3;}");

		ProgramState programState = new ProgramState();

		CodeState finalState;
		try {
			finalState = whileStatement.evaluate(programState);
		} catch (CannotSolveException e) {
			// cannot implement this now, need to simplify something like
			// 2*n+3^n-10
			e.printStackTrace();
		}
		// assertEquals(5,
		// ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testSeparatedNestedLoops() throws Exception {
		// j variable is defined inside the outer loop,
		// so it should not be placeholded for inner loop
		// also, i variable is not used in inner loop, j variable is not used in
		// outer loop
		StateTransition whileStatement = JavaParser
				.parse("int i = 7; while(i != 8) {int j = 9; i = i + 1; while (j != 13) j = j + 1;}");

		ProgramState programState = new ProgramState();

		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(8, ((IntegerValueExpression) finalState.variableValue("i")).value);
	}

	@Test
	public void testNestedLoopsSimplified() throws Exception {
		// i variable is not used in inner loop, j variable is not used in outer
		// loop
		StateTransition whileStatement = JavaParser
				.parse("int i = 7; int j = 9; while(i != 8) {i = i + 1; while (j != 13) {j = j + 1;} }");

		ProgramState programState = new ProgramState();

		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(8, ((IntegerValueExpression) finalState.variableValue("i")).value);
		assertEquals(13, ((IntegerValueExpression) finalState.variableValue("j")).value);
	}

	@Test
	public void testNestedLoops() throws Exception {
		StateTransition whileStatement = JavaParser
				.parse("int i = 1; int j = 1; while (i != 2) {i = i + 1;j = 0; while (j != 12) {j = j + i;}}");

		ProgramState programState = new ProgramState();

		CodeState finalState = whileStatement.evaluate(programState);
		assertEquals(2, ((IntegerValueExpression) finalState.variableValue("i")).value);
		assertEquals(12, ((IntegerValueExpression) finalState.variableValue("j")).value);
	}

}