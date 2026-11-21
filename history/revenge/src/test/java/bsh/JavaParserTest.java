package bsh;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.FunctionCall;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.StateTransition;
import net.sf.metacad.revenge.statement.Assignment;
import net.sf.metacad.revenge.statement.Block;
import net.sf.metacad.revenge.statement.If;
import net.sf.metacad.revenge.statement.Lines;
import net.sf.metacad.revenge.statement.While;
import net.sf.metacad.revenge.type.NumericType;
import net.sf.metacad.revenge.type.PrimitiveTypes;

import org.junit.Test;

public class JavaParserTest {

	@Test
	public void testVariableDefinition() throws Exception {
		String def1 = "int var1;";
		StateTransition statement = JavaParser.parse(def1);
		assertNotNull(statement);
		assertTrue(statement instanceof VariableDefinition);
		assertEquals("var1", ((VariableDefinition) statement).name);
	}

	@Test
	public void testDefineAssignVariable() throws Exception {
		String def1 = "int var1;";
		String ass1 = "var1 = 5;";
		CodeState initialState = JavaParser.evaluate(def1);
		StateTransition statement = JavaParser.parse(ass1, initialState);
		assertNotNull(statement);
		assertTrue(statement instanceof Assignment);
		assertEquals("var1", ((Assignment) statement).getVariableReference().name);
		assertEquals(5, ((IntegerValueExpression) ((Assignment) statement).getRightSideCodeStatement()).value);
	}

	@Test
	public void testDefineAssignUseVariable() throws Exception {
		CodeState initialState = JavaParser.evaluate("int i = 5;");
		StateTransition statement = JavaParser.parse("while (i != 13) i = i + 1;", initialState);
		assertNotNull(statement);
		assertTrue(statement instanceof While);
	}

	@Test
	public void testAssignVariableInline() throws Exception {
		String def1 = "int var1 = 5;";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof VariableDefinition);
		VariableDefinition variable = (VariableDefinition) statement;
		assertEquals("var1", variable.name);
		assertEquals(5, ((IntegerValueExpression) variable.initialValue).value);
	}

	@Test
	public void testAssignVariableInlineDefineAnother() throws Exception {
		String def1 = "int var1 = 5; int var2;";
		StateTransition statements = JavaParser.parse(def1);
		assertTrue(statements instanceof Lines);
		List<? extends StateTransition> codeStatements = ((Lines) statements).getCodeStatements();
		assertEquals(2, codeStatements.size());
		StateTransition statement = codeStatements.get(0);
		VariableDefinition variable = (VariableDefinition) statement;
		assertEquals("var1", variable.name);
		assertEquals(5, ((IntegerValueExpression) variable.initialValue).value);
		StateTransition statement2 = codeStatements.get(1);
		VariableDefinition variable2 = (VariableDefinition) statement2;
		assertEquals("var2", variable2.name);
		assertEquals(MetaExpression.DEFINED_BUT_NOT_INITIALIZED_VARIABLE, variable2.initialValue);
	}

	@Test
	public void testAssignVariableExpression() throws Exception {
		String def1 = "int var1 = 3 + 2;";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof VariableDefinition);
		VariableDefinition variable = (VariableDefinition) statement;
		assertEquals("var1", variable.name);
		assertTrue(variable.initialValue instanceof IntegerExpression);
	}

	@Test
	public void testAssignVariableBooleanExpression() throws Exception {
		String def1 = "boolean var1 = true || false;";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof VariableDefinition);
		VariableDefinition variable = (VariableDefinition) statement;
		assertEquals("var1", variable.name);
		assertEquals(BooleanValueExpression.TRUE, variable.initialValue);
	}

	@Test
	public void testConstant() throws Exception {
		String def1 = "42;";
		StateTransition expression = JavaParser.parse(def1);
		assertTrue(expression instanceof IntegerValueExpression);
		assertEquals(42, ((IntegerValueExpression) expression).value);
	}

	@Test
	public void testBooleanExpression() throws Exception {
		String def1 = "3==5;";
		StateTransition expression = JavaParser.parse(def1);
		assertTrue(expression instanceof BooleanValueExpression);
		assertEquals(BooleanValueExpression.FALSE, expression);
	}

	@Test
	public void testIf() throws Exception {
		String def1 = "if (true) 42;";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof If);
		If ifStatement = (If) statement;
		assertTrue(ifStatement.getIfClause() instanceof BooleanValueExpression);
		assertTrue(ifStatement.getIfBody() instanceof IntegerValueExpression);
		assertEquals(BooleanValueExpression.TRUE, (ifStatement.getIfClause()));
		assertEquals(42, ((IntegerValueExpression) ifStatement.getIfBody()).value);
	}

	@Test
	public void testWhile() throws Exception {
		String def1 = "while (true) 42;";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof While);
		While whileStatement = (While) statement;
		assertTrue(whileStatement.getWhileClause() instanceof BooleanValueExpression);
		assertTrue(whileStatement.getWhileBody() instanceof IntegerValueExpression);
		assertEquals(BooleanValueExpression.TRUE, (whileStatement.getWhileClause()));
		assertEquals(42, ((IntegerValueExpression) whileStatement.getWhileBody()).value);
	}

	@Test
	public void testBlock() throws Exception {
		String def1 = "{int var1 = 42; int var2 = 43;}";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof Block);
		Block blockStatement = (Block) statement;
		assertEquals(2, blockStatement.getCodeStatements().size());
	}

	@Test
	public void testFunctionDefinition() throws Exception {
		String def1 = "void foo() {}";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof FunctionDefinition);
		FunctionDefinition functionDefinition = (FunctionDefinition) statement;
		assertEquals("foo", functionDefinition.functionName);
		assertEquals(PrimitiveTypes.VOID, functionDefinition.returnType);
	}

	@Test
	public void testFunctionDefinitionWithParametersAndReturn() throws Exception {
		String def1 = "int foo(int a, int b) {return a+b;}";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof FunctionDefinition);
		FunctionDefinition functionDefinition = (FunctionDefinition) statement;
		assertEquals("foo", functionDefinition.functionName);
		assertEquals(NumericType.INT, functionDefinition.returnType);
		assertEquals(2, functionDefinition.parameterDefinitions.size());
		assertEquals(1, ((Block) functionDefinition.functionBody).getCodeStatements().size());
	}

	@Test
	public void testFunctionCall() throws Exception {
		String def1 = "foo();";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof FunctionCall);
	}

	@Test
	public void testFunctionCallWithParameters() throws Exception {
		String def1 = "foo(2,3);";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof FunctionCall);
		FunctionCall functionCall = (FunctionCall) statement;
		assertEquals(2, functionCall.getParameterValues().size());
	}

	@Test
	public void testRecursiveFunctionCall() throws Exception {
		String def1 = "void foo(int a) {if (a < 0) foo(a - 1);};";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof FunctionDefinition);
		FunctionDefinition functionDef = (FunctionDefinition) statement;
		assertEquals(1, functionDef.parameterDefinitions.size());
	}

	@Test
	public void testDoubleDivision() throws Exception {
		// TODO handle cast and truncate
		// String def1 = "int var1 = 3*(2/6)/9;";
		String def1 = "int var1 = 3*(2/6);";
		StateTransition statement = JavaParser.parse(def1);
		assertTrue(statement instanceof VariableDefinition);
		VariableDefinition variable = (VariableDefinition) statement;
		assertEquals("var1", variable.name);
		assertTrue(variable.initialValue instanceof IntegerExpression);
	}

}
