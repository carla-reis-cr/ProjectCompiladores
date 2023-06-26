/**
 * Classe: NodoPilhaSemantica
 *
 * Esta classe modela objetos que formarao a pilha semantica.
 *
 * @author Alexandre Zamberlam
 * @author Alunos da disciplina de Compiladores Feevale/2020 1 sem.
 * @author Ricardo Ferreira de Oliveira
 *
 * @version 1.0
 */
/**
 * Nodo da pilha semantica
 *
 */
public class NodoPilhaSemantica {


    private String codigo;
    private int regraQueEmpilhou;

    public NodoPilhaSemantica() {

    }

    public NodoPilhaSemantica( String c, int r ) {

        codigo = new String( c );
        regraQueEmpilhou = r;
    }

    /**
     * @return Retorna o codigo objeto empilhado.
     */
    public String getCodigo() {
        return codigo;
    }
    /**
     * @param codigo o codigo a ser empilhado.
     */
    public void setCodigo(String codigo) {
        this.codigo = new String( codigo );
    }
    /**
     * @return Retorna a regra que empilhou o codigo.
     */
    public int getRegraQueEmpilhou() {
        return regraQueEmpilhou;
    }
    /**
     * @param regraQueEmpilhou numero da regra que empilhou o codigo.
     */
    public void setRegraQueEmpilhou(int regraQueEmpilhou) {
        this.regraQueEmpilhou = regraQueEmpilhou;
    }
     
    /**
     * @return Retorna o codigo objeto empilhado.
     */
    public String getCodigoMinusculo() {
        return codigo.toLowerCase();
    }

}