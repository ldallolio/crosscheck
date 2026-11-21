package net.sf.metacad.revenge.constraint;

public class UnFeasibleException extends Exception {

	private static final long serialVersionUID = 6643654929239845352L;

	public UnFeasibleException() {
		super();
	}

	public UnFeasibleException(String message, Throwable cause) {
		super(message, cause);
	}

	public UnFeasibleException(String message) {
		super(message);
	}

	public UnFeasibleException(Throwable cause) {
		super(cause);
	}

}
