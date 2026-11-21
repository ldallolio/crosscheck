package net.sf.metacad.revenge.constraint;

import java.lang.reflect.Method;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Stack;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.Variable;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;
import choco.kernel.solver.Solver;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.PlaceholderExpression;
import net.sf.metacad.revenge.expression.SymbolicExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.NotExpression;

/**
 * TODO : split in two classes by the two interfaces, by using model as data passed from the first to the second.
 * ConstraintSolver must contain the solver variable
 *
 * @author Luca Dall'Olio
 *
 */
public class ChocoConstraintVisitor implements CodeExpressionVisitor, ConstraintSolver {

	private static final int MAX_CP_INT_DOMAIN = 500;

	private final Model model = new CPModel();

	private final Solver solver = new CPSolver();

	private final Map<String, Variable> vars = new LinkedHashMap<>();

	private final Map<String, String> binding = new LinkedHashMap<>();

	private final Stack<Object> constraints = new Stack<>();

	@Override
	public void compare(ComparisonExpression expression) {
		expression.leftSide.accept(this);
		Object leftside = constraints.pop();
		expression.rightSide.accept(this);
		Object rightside = constraints.pop();
		Constraint constraint = null;
		String chocoMethodName = null;
		switch (expression.operator) {
		case NOTEQUAL:
			chocoMethodName = "neq";
			break;
		case LESSEREQUALTHAN:
			chocoMethodName = "leq";
			break;
		case LESSERTHAN:
			chocoMethodName = "lt";
			break;
		case EQUAL:
			chocoMethodName = "eq";
			break;
		case GREATEREQUALTHAN:
			chocoMethodName = "geq";
			break;
		case GREATERTHAN:
			chocoMethodName = "gt";
			break;
		default:
			throw new UnsupportedOperationException();
		}
		Method chochoMethod = null;
		try {
			chochoMethod = Choco.class.getMethod(chocoMethodName, adaptChocoArgumentType(leftside.getClass()),
					adaptChocoArgumentType(rightside.getClass()));

			constraint = (Constraint) chochoMethod.invoke(null, leftside, rightside);
		} catch (NoSuchMethodException nsme) {
			throw new IllegalStateException(nsme);
		} catch (Exception ex) {
			throw new IllegalStateException(ex);
		}
		constraints.push(constraint);
	}

	private Class<?> adaptChocoArgumentType(Class<?> original) {
		Class<?> adapted = null;
		if (Variable.class.isAssignableFrom(original)) {
			adapted = IntegerExpressionVariable.class;
		}
		if (Integer.class.isAssignableFrom(original)) {
			adapted = Integer.TYPE;
		}
		if (adapted == null) {
			adapted = original;
		}
		return adapted;
	}

	@Override
	public void negate(NotExpression negated) {
		negated.rightSide.accept(this);
		Constraint rightside = (Constraint) constraints.pop();
		Constraint constraint = Choco.not(rightside);
		constraints.push(constraint);
	}

	@Override
	public void compose(BinaryBooleanExpression expression) {
		expression.getLeftSide().accept(this);
		Object leftside = constraints.pop();
		expression.getRightSide().accept(this);
		Object rightside = constraints.pop();
		Constraint constraint = null;
		String chocoMethodName = null;
		switch (expression.operator) {
		case AND:
			chocoMethodName = "and";
			break;
		case OR:
			chocoMethodName = "or";
			break;
		default:
			throw new UnsupportedOperationException("Operator : [" + expression.operator + "] not yet implemented.");
		}
		Method chochoMethod = null;
		try {
			chochoMethod = Choco.class.getMethod(chocoMethodName, adaptChocoArgumentType(leftside.getClass()),
					adaptChocoArgumentType(rightside.getClass()));
			constraint = (Constraint) chochoMethod.invoke(null, leftside, rightside);
		} catch (NoSuchMethodException nsme) {
			throw new IllegalStateException(nsme);
		} catch (Exception ex) {
			throw new IllegalStateException(ex);
		}
		constraints.push(constraint);
	}

	@Override
	public void arithmeticCondition(CodeExpression expression) {
		if (expression instanceof IntegerValueExpression) {
			constraints.push(new Integer(((IntegerValueExpression) expression).value));
		} else if (expression instanceof BinaryIntegerExpression) {
			BinaryIntegerExpression binaryArithmeticExpression = (BinaryIntegerExpression) expression;
			binaryArithmeticExpression.leftSide.accept(this);
			Object leftside = constraints.pop();
			binaryArithmeticExpression.rightSide.accept(this);
			Object rightside = constraints.pop();
			String chocoMethodName = null;
			switch (binaryArithmeticExpression.operator) {
			case PLUS:
				chocoMethodName = "plus";
				break;
			case MINUS:
				chocoMethodName = "minus";
				break;
			case TIMES:
				chocoMethodName = "mult";
				break;
			default:
				throw new UnsupportedOperationException();
			}
			Method chochoMethod = null;
			try {
				chochoMethod = Choco.class.getMethod(chocoMethodName, adaptChocoArgumentType(leftside.getClass()),
						adaptChocoArgumentType(rightside.getClass()));
				constraints.push(chochoMethod.invoke(null, leftside, rightside));
			} catch (NoSuchMethodException nsme) {
				throw new IllegalStateException(nsme);
			} catch (Exception ex) {
				throw new IllegalStateException(ex);
			}

		} else {
			throw new UnsupportedOperationException("not yet implemented");
		}
	}

	@Override
	public void useVariable(PlaceholderExpression expression) {
		String placeholderName = expression.getName();
		if (!binding.containsKey(placeholderName)) {
			throw new IllegalArgumentException("No binding for : [" + placeholderName + "]");
		}

		constraints.push(vars.get(binding.get(placeholderName)));
	}

	@Override
	public Map<String, CodeExpression> solve(String minimizeVariableName) throws UnFeasibleException {
		Map<String, CodeExpression> solution = new LinkedHashMap<>();
		solver.read(model);
		System.out.println("while problem : " + solver.pretty());
		solver.minimize(solver.getVar((IntegerVariable) vars.get(minimizeVariableName)), true);
		for (String variableName : vars.keySet()) {
			int value = solver.getVar((IntegerVariable) vars.get(variableName)).getVal();
			System.out.println("Variable : [" + variableName + "] has solution : [" + value + "]");
			solution.put(variableName, new IntegerValueExpression(value));
		}

		if (!solver.isFeasible().booleanValue()) {
			// TODO handle not feasible problems somehow
			throw new UnFeasibleException("Problem is not feasible");
		}

		return solution;
	}

	@Override
	public void bindVariable(String constraintVariableName, String localNameIgnored, String placeholderName) {

		if (binding.containsKey(placeholderName)) {
			throw new IllegalStateException("Placeholder : [" + placeholderName + "] already bound to : ["
					+ binding.get(placeholderName) + "], cannot bind it to : [" + constraintVariableName + "]");
		}

		// Lazily create a new problem variable
		// variable name cannot simply be placeholder's name, because the same
		// expression can be considered multiple times, binding the same
		// placeolder to different constraint variables, example :
		//
		// while(i <= 500) ...
		//
		// makes two different constraint for the same placeholder :
		// i_prefinal <= 500 and i_final > 500
		if (!vars.containsKey(constraintVariableName)) {
			// TODO handle non integer variables
			IntegerVariable integerVariable = Choco.makeIntVar(constraintVariableName, -1 * MAX_CP_INT_DOMAIN, 500,
					"cp:bound");
			model.addVariable(integerVariable);
			vars.put(constraintVariableName, integerVariable);
		}

		binding.put(placeholderName, constraintVariableName);
	}

	@Override
	public void clearBindings() {
		binding.clear();
	}

	@Override
	public void constrain(CodeExpression expression) {
		expression.accept(this);
		model.addConstraint((Constraint) constraints.pop());
	}

	@Override
	public void repeat(CodeExpression expression, IntegerExpression times, Map<String, CodeExpression> initialValues) {
		expression.repeat(times, this, initialValues);
	}

	@Override
	public void follow(CodeExpression expression) {
		expression.accept(this);
	}

	@Override
	public void useVariable(VariableReference expression) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void useSymbol(SymbolicExpression expression) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void callFunction(String functionName, CodeExpression[] parameterValues) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void bindFunction(String constraintVariableName, String constraintVariableLocalName,
			String placeholderName) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void stopAt(CodeExpression expression) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void setMinimize(VariableReference placeholderName) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

}