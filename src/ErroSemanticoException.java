public class ErroSemanticoException extends Exception {
 
    private static final long serialVersionUID = -2346384470483785588L;
 
    public ErroSemanticoException() {
        super("Erro semantico!");
    }
 
    public ErroSemanticoException(String message) {
        super(message);
    }
 
    public ErroSemanticoException(Throwable t) {
        super(t);
    }
}
