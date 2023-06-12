public class ErroLexicoException extends Exception {

    private static final long serialVersionUID = -2346384470483785588L;

    public ErroLexicoException() {
        super("Erro léxico!");
    }

    public ErroLexicoException(String message) {
        super(message);
    }

    public ErroLexicoException(Throwable t) {
        super(t);
    }
}
