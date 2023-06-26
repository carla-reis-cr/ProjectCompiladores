import java.util.Iterator;
import java.util.Stack;

/**
 * Classe: Pilha Semantica
 *
 * Esta classe modela a pilha semantica.
 *
 * @author Ricardo Ferreira de Oliveira
 * @author Turma de projeto de compiladores 1/2023
 *
 */

public class PilhaSemantica {

    private Stack pilha;

    private StringBuffer saidaPilhaSemantica;

    public PilhaSemantica() {
        pilha = new Stack();
    }

    public NodoPilhaSemantica pop() {

        NodoPilhaSemantica nodo;
        nodo = ( NodoPilhaSemantica ) pilha.pop();
        System.out.println( "Desempilhou " + nodo.getCodigo() );

        return( nodo );
    }

    public NodoPilhaSemantica push( String c, int r ) {

        System.out.println( "Empilhou: " + c );

        NodoPilhaSemantica nodo = new NodoPilhaSemantica( c, r );
        pilha.push( nodo );
        return( nodo );
    }

    public NodoPilhaSemantica push( NodoPilhaSemantica nodo ) {

        System.out.println( "Empilhou: " + nodo.getCodigo() );

        pilha.push( nodo );
        return( nodo );
    }

    public void listaPilha() {
        System.out.println( "[=======================]");
        Iterator i = pilha.iterator();
        while ( i.hasNext() ) {
            NodoPilhaSemantica n = (NodoPilhaSemantica) i.next();
            System.out.println( "[ "+n.getCodigo()+") ]" );
        }
        System.out.println( "[#######################]");
    }

}