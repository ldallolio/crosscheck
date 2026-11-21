package net.sf.metacad.revenge.expression;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import bsh.JavaParser;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.state.StateTransition;

public class FunctionCallTest {

	@Test
	public void testEvaluateEmptyFunction() throws Exception {
		String code = "void foo() {}; foo();";
		JavaParser.evaluate(code);
	}

	@Test
	public void testEvaluateConstantReturnFunction() throws Exception {
		String code = "int foo() {return 7;}; foo();";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertEquals(7, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testEvaluateWithReturnCalculatedFunction() throws Exception {
		String code = "int foo(int a) {return a;}; foo(5);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertEquals(5, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testEvaluateWithReturnCalculatedFromParametersFunction() throws Exception {
		String code = "int foo(int a, int b) {return a+b;}; foo(7,5);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertFalse(evaluatedState.isVariableDefined("a"));
		assertFalse(evaluatedState.isVariableDefined("b"));
		assertEquals(12, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testEvaluateWithReturnCalculatedFromParametersAndMuteVariableFunction() throws Exception {
		String code = "int foo(int a, int b) {int c = a+b;return c;}; foo(9,2);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertFalse(evaluatedState.isVariableDefined("a"));
		assertFalse(evaluatedState.isVariableDefined("b"));
		assertFalse(evaluatedState.isVariableDefined("c"));
		assertEquals(11, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testEvaluateWithNestedFunction() throws Exception {
		String code = "int goo(int a, int b) {return a+b;}; int foo(int a, int b) {int c = goo(a,b);return c;}; foo(11,3);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertFalse(evaluatedState.isVariableDefined("a"));
		assertFalse(evaluatedState.isVariableDefined("b"));
		assertFalse(evaluatedState.isVariableDefined("c"));
		assertEquals(14, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testRecursiveFunction() throws Exception {

		String code = "int foo(int a) {if (a > 2) a = foo(a - 2); return a;}; foo(5);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertEquals(1, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testRecursiveFunctionWithExpressions() throws Exception {

		String code = "int foo(int a) {if (a > 4) a = foo(a - 2) + 3; return a + 6;}; foo(50);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertEquals(217, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testInfiniteRecursiveFunction() throws Exception {

		String code = "int foo(int a) {if (a > 1) a = foo(a + 1); return a;}; foo(3);";
		StateTransition stateTransition = JavaParser.parse(code);
		try {
			stateTransition.evaluate(new ProgramState());
			assertTrue(false);
		} catch (UnFeasibleException e) {
			assertTrue(true);
		}
	}

	@Test
	public void testSingleRecursion() throws Exception {
		String code = "int foo(int n) {if (n == 1) return 42; return foo(1);}; foo(5);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertEquals(42, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	// @Test
	public void testRecursionReturnExpression() throws Exception {
		String code = "int foo(int n) {if (n == 0) return 1; return foo(n - 1) + 1;}; foo(5);";
		CodeState evaluatedState = JavaParser.evaluate(code);
		assertEquals(6, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}

	@Test
	public void testFactorial() throws Exception {
		String code = "int factorial(int n) {if (n == 0) return 1; return factorial(n - 1) * n;}; factorial(5);";
		StateTransition stateTransition = JavaParser.parse(code);
		CodeState evaluatedState = stateTransition.evaluate(new ProgramState());
		CodeExpression result = evaluatedState.getLeftValue();
		// TODO Should be 120, after manual search/replacing ? using a special
		// factorial function, only showing last part of recursion ?
		assertTrue(result instanceof RepeatedExpression);
	}

	@Test
	public void testFibonacci() throws Exception {
		String code = "int fibonacci(int n) {if (n == 0) return 0; if (n == 1) return 1; return fibonacci(n - 1) + fibonacci(n - 2);}; fibonacci(5);";
		StateTransition stateTransition = JavaParser.parse(code);
		CodeState evaluatedState = stateTransition.evaluate(new ProgramState());
		assertEquals(1, ((IntegerValueExpression) evaluatedState.getLeftValue()).value);
	}
}