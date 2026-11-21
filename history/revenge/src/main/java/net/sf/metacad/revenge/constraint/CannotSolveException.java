package net.sf.metacad.revenge.constraint;

public class CannotSolveException extends Exception {

	private static final long serialVersionUID = -7089074350363888142L;

	public CannotSolveException() {
		super();
	}

	public CannotSolveException(String message, Throwable cause) {
		super(message, cause);
	}

	public CannotSolveException(String message) {
		super(message);
	}

	public CannotSolveException(Throwable cause) {
		super(cause);
	}
}
