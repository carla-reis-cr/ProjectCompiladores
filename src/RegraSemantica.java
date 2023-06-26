
import java.io.UnsupportedEncodingException;
import java.util.HashMap;

import javax.swing.filechooser.FileFilter;
import java.io.FileNotFoundException;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import javax.swing.JTextArea;
import java.io.IOException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.File;

/**
 * Sintatico - Primeira versao do sintatico
 *
 * @author Ricardo Ferreira de Oliveira
 * @author Turma de projeto de compiladores 1/2023
 *
 *
 *         gramatica:
 *
 *         <G> ::= 'PROGRAM''{' <bloco> '}''END'
 *         <bloco> ::= <declaracoes> 'BEGIN' <comandos> 'END'
 *         |'BEGIN' <comandos> 'END'
 *         <declaracoes>::= 'DECLARE' <declara_var>';''
 *         <declara_var>::= <variavel> | <declara_var>, <variavel> | <variavel>
 *         ':=' <expr>';'
 *         <variavel> ::= <ident>
 *         <comandos> ::= <declara_var>|<condicional> |<ler> | <escrever> |
 *         <enquanto>
 *         <condicional>::= 'IF' <condicao> 'THEN' <comandos> 'ENDIF'
 *         |'IF' <condicao> 'THEN' <comandos> 'ELSE' <comandos> 'ENDIF'
 *         <ler> ::= 'READ''('<variaveis>')'';'
 *         <escrever> ::= 'WRITE''('<expr>')'';'
 *         <enquanto> ::= 'WHILE''('<condicao>'')''{'<comandos>'}'
 *         |'DO''{'<comandos>'}''WHILE''('<condicao>')'
 *         <condicao> ::= <expr> '>' <expr>
 *         |<expr> '>='<expr>
 *         |<expr> '<>'<expr>
 *         |<expr> '<='<expr>
 *         |<expr> '<' <expr>
 *         |<expr> '=='<expr>
 *         <expr> ::= <expr> + <terminal>
 *         |<expr> - <terminal>
 *         |<terminal>
 *         <terminal> ::= <terminal> * <fator>
 *         |<terminal> / <fator>
 *         |<terminal> % <fator>
 *         |<F>
 *         <fator> ::= -<X>
 *         | <X> ** <fator>
 *         | <X>
 *         <X> ::= '(' <expr> ')'
 *         | [0-9]+('.'[0-9]+)
 *         | <variavel>
 *         <id> ::= [A-Z]+([A-Z]_[0-9]*)
 * 
 */
public class RegraSemantica {

    // Lista de tokens
    static final int T_PROGRAMA = 1; // 'PROGRAM'
    static final int T_ABRE_CHAVES = 2; // '{'
    static final int T_FECHA_CHAVES = 3; // '}'
    static final int T_FIM = 4; // 'END'
    static final int T_INICIO = 5; // 'BEGIN'
    static final int T_DECLARA = 6; // 'DECLARE'
    static final int T_PONTO_VIRGULA = 7; // ';'
    static final int T_IDENTIFICADOR = 8; // [A-Z]+([A-Z]_[0-9]*)
    static final int T_VIRGULA = 9; // ','
    static final int T_ATRIBUICAO = 10; // ':='
    static final int T_IF = 11; // 'IF'
    static final int T_THEN = 12; // 'THEN'
    static final int T_ENDIF = 13; // 'ENDIF'
    static final int T_ELSE = 14; // 'ELSE'
    static final int T_READ = 15; // 'READ'

    static final int T_ABRE_PARENTESES = 16;// '('
    static final int T_FECHA_PARENTESES = 17;// '('
    static final int T_WRITE = 18; // 'WRITE'
    static final int T_WHILE = 19;// 'WHILE'
    static final int T_DO = 20;// 'DO'
    static final int T_MAIOR = 21; // '>'
    static final int T_MAIOR_IGUAL = 22;// '>='
    static final int T_DIFERENTE = 23;// '<>'
    static final int T_MENOR_IGUAL = 24;// '<=
    static final int T_MENOR = 25;// '<'
    static final int T_IGUAL = 26;// '=='
    static final int T_MAIS = 27;// '+'
    static final int T_MENOS = 28;// '-'
    static final int T_VEZES = 29;// '*'
    static final int T_DIVIDIDO = 30;// '/'
    static final int T_RESTO = 31;// '-'
    static final int T_ELEVADO = 32;// '**'
    static final int T_NUMERO = 33;

    // Lista tokens abertura arquivo e erros léxicos
    static final int T_FIM_FONTE = 90;
    static final int T_ERRO_LEX = 98;
    static final int T_NULO = 99;

    static final int FIM_ARQUIVO = 26;

    static final int E_SEM_ERROS = 0;
    static final int E_ERRO_LEXICO = 1;
    static final int E_ERRO_SINTATICO = 2;

    // Variaveis que surgem no Lexico
    static File arqFonte;
    static BufferedReader rdFonte;
    static File arqDestinoLex;
    static File arqDestinoSem;
    static char lookAhead;
    static int token;

    static String lexema;
    static int ponteiro;
    static String linhaFonte;
    static int linhaAtual;
    static int colunaAtual;
    static String mensagemDeErro;
    static StringBuffer tokensIdentificados = new StringBuffer();

    static int tokenAnterior;

    // Variaveis adicionadas para o sintatico
    static StringBuffer regrasReconhecidas = new StringBuffer();
    static int estadoCompilacao;

    // Variaveis adicionadas para o semantico
    static StringBuffer codigoPascal = new StringBuffer();
    static String ultimoLexema;
    static int nivelIdentacao = 0; // para saber quantos espaços eu dou
    static String exp_0;
    static String exp_1;
    static String exp_2;
    static String exp_alvo;
    static NodoPilhaSemantica nodo;
    static NodoPilhaSemantica nodo_0;
    static NodoPilhaSemantica nodo_1;
    static NodoPilhaSemantica nodo_2;
    static PilhaSemantica pilhaSemantica = new PilhaSemantica();
    static HashMap<String, Integer> tabelaSimbolos = new HashMap<String, Integer>();
    static Boolean isDoWhile = false;

    public static void main(String s[]) throws ErroLexicoException, ErroSemanticoException {
        try {
            abreArquivo();
            abreDestino();
            linhaAtual = 0;
            colunaAtual = 0;
            ponteiro = 0;
            linhaFonte = "";
            token = T_NULO;
            mensagemDeErro = "";
            tokensIdentificados.append("Tokens reconhecidos: \n\n");
            regrasReconhecidas.append("\n\nRegras reconhecidas: \n\n");
            estadoCompilacao = E_SEM_ERROS;

            // posiciono no primeiro token
            movelookAhead();
            buscaProximoToken();

            analiseSintatica();

            exibeSaida();

            gravaSaida(arqDestinoLex);
            gravaSaida(arqDestinoSem);

            fechaFonte();

        } catch (FileNotFoundException fnfe) {
            JOptionPane.showMessageDialog(null, "Arquivo nao existe!", "FileNotFoundException!",
                    JOptionPane.ERROR_MESSAGE);
        } catch (UnsupportedEncodingException uee) {
            JOptionPane.showMessageDialog(null, "Erro desconhecido", "UnsupportedEncodingException!",
                    JOptionPane.ERROR_MESSAGE);
        } catch (IOException ioe) {
            JOptionPane.showMessageDialog(null, "Erro de io: " + ioe.getMessage(), "IOException!",
                    JOptionPane.ERROR_MESSAGE);
        } catch (ErroLexicoException ele) {
            JOptionPane.showMessageDialog(null, ele.getMessage(), "Erro Lexico Exception!", JOptionPane.ERROR_MESSAGE);
        } catch (ErroSintaticoException ese) {
            JOptionPane.showMessageDialog(null, ese.getMessage(), "Erro Sintático Exception!",
                    JOptionPane.ERROR_MESSAGE);
        } catch (ErroSemanticoException esme) {
            JOptionPane.showMessageDialog(null, esme.getMessage(), "Erro Semantico Exception!",
                    JOptionPane.ERROR_MESSAGE);
        } finally {
            System.out.println(codigoPascal);

            System.out.println("Execucao terminada!");
        }
    }

    static void analiseSintatica()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

        g();

        if (estadoCompilacao == E_ERRO_LEXICO) {
            JOptionPane.showMessageDialog(null, mensagemDeErro, "Erro Lexico!", JOptionPane.ERROR_MESSAGE);
        } else if (estadoCompilacao == E_ERRO_SINTATICO) {
            JOptionPane.showMessageDialog(null, mensagemDeErro, "Erro Sintatico!", JOptionPane.ERROR_MESSAGE);
        } else {
            JOptionPane.showMessageDialog(null, "Analise Sintatica terminada sem erros", "Analise Sintatica terminada!",
                    JOptionPane.INFORMATION_MESSAGE);
            acumulaRegraSintaticaReconhecida("<G>");
        }
    }

    // <G> ::= 'PROGRAM''{' <bloco> '}''END'
    private static void g() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        if (token == T_PROGRAMA) {
            buscaProximoToken();
            regraSemantica(0);
            if (token == T_ABRE_CHAVES) {
                buscaProximoToken();
                bloco();
                if (token == T_FECHA_CHAVES) {
                    buscaProximoToken();
                    if (token == T_FIM) {
                        buscaProximoToken();
                        acumulaRegraSintaticaReconhecida("<G> ::= 'PROGRAM''{' <bloco> '}''END'");
                    } else {
                        registraErroSintatico(
                                "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                        + linhaFonte + ">\n'END' esperado, mas encontrei: " + lexema);
                    }
                } else {
                    registraErroSintatico(
                            "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                    + linhaFonte + ">\n'}' esperado, mas encontrei: " + lexema);
                }
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n'{' esperado, mas encontrei: " + lexema);
            }
        } else {
            registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                    + linhaFonte + ">\n'PROGRAM' esperado, mas encontrei: " + lexema);
        }

    }

    // <bloco> ::= <declaracoes> 'BEGIN' <comandos> 'END'
    // |'BEGIN' <comandos> 'END'
    private static void bloco()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        declaracoes();

        if (token == T_INICIO) {

            buscaProximoToken();
            regraSemantica(28);
            if (token == T_IDENTIFICADOR) {
                tokenAnterior = token;
                buscaProximoToken();
                if (tokenAnterior == T_IDENTIFICADOR || token == T_ATRIBUICAO) {
                    tokenAnterior = T_ATRIBUICAO;

                    comandos();
                }
            }
            while (!(token == T_FIM)) {
                if (token == T_FECHA_CHAVES) {
                    regraSemantica(29);
                    return;
                } else {
                    if (token == T_IF || token == T_READ || token == T_WRITE || token == T_WHILE || token == T_DO
                            || token == T_DECLARA) {
                        comandos();
                        buscaProximoToken();
                    } else {
                        buscaProximoToken();
                        comandos();
                    }
                }
            }

            if (token == T_FIM) {
                buscaProximoToken();
                regraSemantica(29);

                acumulaRegraSintaticaReconhecida("'BEGIN' <comandos> 'END'");
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n'END' esperado, mas encontrei: " + lexema);
            }

        } else {
            registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                    + linhaFonte + ">\n'BEGIN' esperado, mas encontrei: " + lexema);
        }
    }

    // <declaracoes>::= 'DECLARE' <declara_var>';''
    private static void declaracoes()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        if (token == T_DECLARA) {
            buscaProximoToken();
            regraSemantica(1);
            declara_var();
            if (token == T_PONTO_VIRGULA) {
                buscaProximoToken();
                regraSemantica(27);
                acumulaRegraSintaticaReconhecida("'DECLARE' <declara_var>';'");
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n'DECLARE...;' esperado, mas encontrei: " + lexema);
            }
        }
    }

    // <declara_var>::= <variavel> | <variavel>,<declara_var> | <variavel> ':='
    // <expr>';'
    private static void declara_var()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        boolean outraRegra = false;
        if (tokenAnterior == T_ATRIBUICAO) {
            buscaProximoToken();
            expr();

            if (token == T_PONTO_VIRGULA) {

                buscaProximoToken();
                regraSemantica(3);
                acumulaRegraSintaticaReconhecida("<variavel> ':=' <expr>';'");
                return;
            }
        } else {
            variavel();

        }
        while (token == T_VIRGULA) {
            regraSemantica(26);
            buscaProximoToken();
            declara_var();
            acumulaRegraSintaticaReconhecida("<declara_var>::= <variavel>,<declara_var>");
            outraRegra = true;
        }
        if (token == T_ATRIBUICAO) {
            buscaProximoToken();
            expr();
            regraSemantica(3);
            acumulaRegraSintaticaReconhecida("<declara_var>::= <variavel> ':=' <expr>");
            outraRegra = true;
        } else {
            if (token == T_PONTO_VIRGULA) {
                return;
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n':=' esperado, mas encontrei: " + lexema);
            }
        }
        if (!outraRegra) {
            acumulaRegraSintaticaReconhecida("<declara_var>::= <variavel>");
        }
    }

    // <variavel> ::= <ident>
    private static void variavel()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        ident();
        regraSemantica(2);
        acumulaRegraSintaticaReconhecida("<variavel>   ::= <ident>");
    }

    // <ident> ::= [A-Z]+([A-Z]_[0-9]*)
    private static void ident() throws IOException, ErroLexicoException, ErroSintaticoException {
        if (token == T_IDENTIFICADOR) {
            buscaProximoToken();
            acumulaRegraSintaticaReconhecida("<ident>      ::= [A-Z]+([A-Z]_[0-9]*)");
        } else {
            registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                    + linhaFonte + ">\nEsperava um identificador. Encontrei: " + lexema);
        }
    }

    // <comandos> ::= <declara_var>|<condicional> |<ler> | <escrever> | <enquanto>
    private static void comandos()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        // regraSemantica(18);

        switch (token) {
            case T_IF:
                condicional();
                break;
            case T_READ:
                ler();
                break;
            case T_WRITE:
                escrever();
                break;
            case T_WHILE:
                enquanto();
                break;
            case T_DO:
                faca_enquanto();
                break;
            case T_DECLARA:
                declara_var();
                break;
            default:
                switch (tokenAnterior) {
                    case T_ATRIBUICAO:
                        regraSemantica(33);
                        token = tokenAnterior;
                        declara_var();
                        break;
                    default:
                        registraErroSintatico("Erro Sintatico na linha: " + linhaAtual
                                + "\nReconhecido ao atingir a coluna: "
                                + colunaAtual + "\nLinha do Erro: <" + linhaFonte
                                + ">\nComando nao identificado va aprender a programar pois encontrei: " + lexema);
                }
        }
        acumulaRegraSintaticaReconhecida(
                "<comandos> 	 ::= <declara_var>|<condicional> |<ler> | <escrever> | <enquanto>");
    }

    // <condicional>::= 'IF' <condicao> 'THEN' <comandos> 'ENDIF'
    // |'IF' <condicao> 'THEN' <comandos> 'ELSE' <comandos> 'ENDIF'
    private static void condicional()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

        if (token == T_IF) {
            buscaProximoToken();
            condicao();
            regraSemantica(17);
            if (token == T_THEN) {
                buscaProximoToken();
                // regraSemantica(18);

                while (!(token == T_ELSE || token == T_ENDIF)) {
                    if (token == T_IDENTIFICADOR) {
                        tokenAnterior = token;
                        buscaProximoToken();
                        if (tokenAnterior == T_IDENTIFICADOR || token == T_ATRIBUICAO) {
                            tokenAnterior = T_ATRIBUICAO;
                            comandos();
                        }
                    } else {
                        comandos();
                        // regraSemantica(16);
                    }
                }
                if (token == T_ELSE) {
                    regraSemantica(16);

                    buscaProximoToken();
                    regraSemantica(31);
                    while (!(token == T_ENDIF)) {
                        if (token == T_IDENTIFICADOR) {
                            tokenAnterior = token;
                            buscaProximoToken();
                            if (tokenAnterior == T_IDENTIFICADOR || token == T_ATRIBUICAO) {
                                tokenAnterior = T_ATRIBUICAO;
                                // regraSemantica(31);
                                comandos();
                            }
                        } else {
                            // regraSemantica(31);
                            comandos();
                        }
                    }

                    if (token == T_ENDIF) {
                        buscaProximoToken();
                        acumulaRegraSintaticaReconhecida(
                                "<condicional>::= 'IF' <condicao> 'THEN' <comandos> 'ELSE' <comandos> 'ENDIF'");
                        regraSemantica(30);
                        // regraSemantica(27);
                    } else {
                        registraErroSintatico(
                                "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                        + linhaFonte + ">\n'ENDIF' esperado, mas encontrei: " + lexema);
                    }
                } else {
                    if (token == T_ENDIF) {
                        buscaProximoToken();
                        acumulaRegraSintaticaReconhecida("<condicional>::= 'IF' <condicao> 'THEN' <comandos> 'ENDIF'");
                        regraSemantica(30);
                        // regraSemantica(27);
                    } else {
                        registraErroSintatico(
                                "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                        + linhaFonte + ">\n'ENDIF' esperado, mas encontrei: " + lexema);
                    }
                }
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n'THEN' esperado, mas encontrei: " + lexema);
            }
        }
    }

    // <ler> ::= 'READ''('<variaveis>')'';'
    private static void ler() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

        if (token == T_READ) {

            buscaProximoToken();
            if (token == T_ABRE_PARENTESES) {
                buscaProximoToken();
                expr();

                if (token == T_FECHA_PARENTESES) {
                    buscaProximoToken();
                    if (token == T_PONTO_VIRGULA) {
                        // buscaProximoToken();
                        acumulaRegraSintaticaReconhecida(
                                "<ler>		 ::= 'READ''('<variaveis>')'';'");
                        regraSemantica(14);

                        regraSemantica(27);
                    } else {
                        registraErroSintatico(
                                "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                        + linhaFonte + ">\n';' esperado, mas encontrei: " + lexema);
                    }
                } else {
                    registraErroSintatico(
                            "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                    + linhaFonte + ">\n')' esperado, mas encontrei: " + lexema);
                }
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n'(' esperado, mas encontrei: " + lexema);
            }
        }
    }

    // <escrever> ::= 'WRITE''('<expr>')'';'
    private static void escrever()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        buscaProximoToken();
        if (token == T_ABRE_PARENTESES) {
            buscaProximoToken();
            expr();
            if (token == T_FECHA_PARENTESES) {
                buscaProximoToken();
                if (token == T_PONTO_VIRGULA) {
                    buscaProximoToken();
                    acumulaRegraSintaticaReconhecida(
                            "<escrever>	 ::= 'WRITE''('<expr>')'';'");
                    regraSemantica(25);
                    regraSemantica(27);

                } else {
                    registraErroSintatico(
                            "Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                                    + linhaFonte + ">\n';' esperado, mas encontrei: " + lexema);
                }
            } else {
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\n')' esperado, mas encontrei: " + lexema);
            }
        } else {
            registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                    + linhaFonte + ">\n'(' esperado, mas encontrei: " + lexema);
        }
    }

    // <enquanto> ::= 'WHILE''('<condicao>'')''{'<comandos>'}'
    private static void enquanto()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        if (token == T_WHILE) {
            buscaProximoToken();
            if (token == T_ABRE_PARENTESES) {
                buscaProximoToken();
                condicao();
                regraSemantica(15);
                if (token == T_FECHA_PARENTESES) {
                    buscaProximoToken();

                    if (token == T_ABRE_CHAVES) {
                        buscaProximoToken();
                        regraSemantica(32);
                        while (!(token == T_FECHA_CHAVES)) {
                            if (token == T_IDENTIFICADOR) {
                                tokenAnterior = token;
                                buscaProximoToken();
                                if (tokenAnterior == T_IDENTIFICADOR || token == T_ATRIBUICAO) {
                                    tokenAnterior = T_ATRIBUICAO;
                                    comandos();
                                    // regraSemantica(16);
                                }
                            } else {
                                comandos();
                                // regraSemantica(16);
                            }
                        }
                        if (token == T_FECHA_CHAVES) {
                            buscaProximoToken();
                            acumulaRegraSintaticaReconhecida(
                                    "<enquanto>	 ::= 'WHILE''('<condicao>'')''{'<comandos>'}' ");
                            regraSemantica(30);
                            // regraSemantica(27);
                        } else {
                            registraErroSintatico("Erro Sintatico na linha: " + linhaAtual
                                    + "\nReconhecido ao atingir a coluna: "
                                    + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'} esperado mas encontrei: "
                                    + lexema);
                        }
                    } else {
                        registraErroSintatico("Erro Sintatico na linha: " + linhaAtual
                                + "\nReconhecido ao atingir a coluna: "
                                + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'{' esperado mas encontrei: "
                                + lexema);
                    }
                } else {
                    registraErroSintatico("Erro Sintatico na linha: " + linhaAtual
                            + "\nReconhecido ao atingir a coluna: "
                            + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n')' esperado mas encontrei: "
                            + lexema);
                }
            } else {
                registraErroSintatico("Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: "
                        + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\n'(' esperado mas encontrei: "
                        + lexema);
            }

        } else {
            registraErroSintatico(
                    "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual
                            + "\nLinha do Erro: <" + linhaFonte + ">\n'WHILE' esperado mas encontrei: " + lexema);
        }
    }

    // <enquanto>::='DO''{'<comandos>'}''WHILE''('<condicao>')'
    private static void faca_enquanto()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

        if (token == T_DO) {
            buscaProximoToken();
            regraSemantica(32);
            isDoWhile = true;

            if (token == T_ABRE_CHAVES) {
                buscaProximoToken();
                while (!(token == T_FECHA_CHAVES)) {
                    if (token == T_IDENTIFICADOR) {
                        tokenAnterior = token;
                        buscaProximoToken();
                        if (tokenAnterior == T_IDENTIFICADOR || token == T_ATRIBUICAO) {
                            tokenAnterior = T_ATRIBUICAO;
                            comandos();
                        }
                    } else {
                        comandos();
                    }
                }
                if (token == T_FECHA_CHAVES) {
                    buscaProximoToken();
                    if (token == T_WHILE) {
                        buscaProximoToken();
                        if (token == T_ABRE_PARENTESES) {
                            buscaProximoToken();
                            condicao();
                            buscaProximoToken();
                            acumulaRegraSintaticaReconhecida(
                                    "<enquanto>::='DO''{'<comandos>'}''WHILE''('<condicao>')'");
                            // regraSemantica(30);
                            // regraSemantica(27);
                            regraSemantica(15);

                        } else {
                            registraErroSintatico(
                                    "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: "
                                            + colunaAtual
                                            + "\nLinha do Erro: <" + linhaFonte + ">\n'(' esperado mas encontrei: "
                                            + lexema);
                        }
                    } else {
                        registraErroSintatico(
                                "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: "
                                        + colunaAtual
                                        + "\nLinha do Erro: <" + linhaFonte + ">\n'WHILE' esperado mas encontrei: "
                                        + lexema);
                    }
                } else {
                    registraErroSintatico(
                            "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: "
                                    + colunaAtual
                                    + "\nLinha do Erro: <" + linhaFonte + ">\n'}' esperado mas encontrei: " + lexema);
                }
            } else {
                registraErroSintatico(
                        "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual
                                + "\nLinha do Erro: <" + linhaFonte + ">\n'{' esperado mas encontrei: " + lexema);
            }

        } else {
            registraErroSintatico(
                    "Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual
                            + "\nLinha do Erro: <" + linhaFonte + ">\n'DO' esperado mas encontrei: " + lexema);
        }

    }

    // <condicao> ::= <expr> '>' <expr>
    // |<expr> '>='<expr>
    // |<expr> '<>'<expr>
    // |<expr> '<='<expr>
    // |<expr> '<' <expr>
    // |<expr> '=='<expr>
    private static void condicao()
            throws ErroLexicoException, IOException, ErroSintaticoException, ErroSemanticoException {
        expr();
        switch (token) {
            case T_MAIOR:
                buscaProximoToken();
                expr();
                regraSemantica(19);
                break;
            case T_MENOR:
                buscaProximoToken();
                expr();
                regraSemantica(20);
                break;
            case T_MAIOR_IGUAL:
                buscaProximoToken();
                expr();
                regraSemantica(21);
                break;
            case T_MENOR_IGUAL:
                buscaProximoToken();
                expr();
                regraSemantica(22);
                break;
            case T_IGUAL:
                buscaProximoToken();
                expr();
                regraSemantica(23);
                break;
            case T_DIFERENTE:
                buscaProximoToken();
                expr();
                regraSemantica(24);
                break;
            default:
                registraErroSintatico("Erro Sintatico. Linha: " + linhaAtual + "\nColuna: " + colunaAtual + "\nErro: <"
                        + linhaFonte + ">\nEsperava um operador logico. Encontrei: " + lexema);
        }
        acumulaRegraSintaticaReconhecida("<CONDICAO> ::= <expr> ('>'|'>='|'<>'|'<='|'<'|'==') <expr> ");
    }

    // <expr> ::= <expr> + <terminal>
    // |<expr> - <terminal>
    // |<terminal>
    private static void expr() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {

        terminal();

        while ((token == T_MAIS) || (token == T_MENOS)) {
            switch (token) {
                case T_MAIS: {
                    buscaProximoToken();
                    terminal();
                    regraSemantica(5);
                }
                    break;
                case T_MENOS: {
                    buscaProximoToken();
                    terminal();
                    regraSemantica(6);
                }
                    break;
            }
        }

        acumulaRegraSintaticaReconhecida("<expr> ::= <expr> + <terminal>|<expr> - <terminal>|<terminal> ");
    }

    // <terminal> ::= <terminal> * <fator>
    // |<terminal> / <fator>
    // |<terminal> % <fator>
    // |<fator>
    private static void terminal()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        fator();
        while ((token == T_VEZES) || (token == T_DIVIDIDO) || (token == T_RESTO)) {
            switch (token) {
                case T_VEZES: {
                    buscaProximoToken();
                    fator();
                    regraSemantica(7);
                }
                    break;
                case T_DIVIDIDO: {
                    buscaProximoToken();
                    fator();
                    regraSemantica(8);
                }
                    break;
                case T_RESTO: {
                    buscaProximoToken();
                    fator();
                    regraSemantica(9);
                }
                    break;

            }
        }

        acumulaRegraSintaticaReconhecida(
                "<terminal> ::= <terminal> * <fator>|<terminal> / <fator>|<terminal> % <fator>|<fator>");
    }

    // <F> ::= -<fator>
    // <F> ::= <X> ** <fator>
    // <F> ::= <X>
    private static void fator()
            throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        if (token == T_MENOS) {
            buscaProximoToken();
            fator();
        } else {
            x();
            while (token == T_ELEVADO) {
                buscaProximoToken();
                x();
                regraSemantica(10);
            }
        }
        acumulaRegraSintaticaReconhecida("<F> ::= -<fator>|<X> ** <fator>|<X> ");

    }

    // <X> ::= '(' <expr> ')'
    // <X> ::= [0-9]+('.'[0-9]+)
    // <X> ::= <variavel>
    private static void x() throws IOException, ErroLexicoException, ErroSintaticoException, ErroSemanticoException {
        switch (token) {
            case T_IDENTIFICADOR:
                buscaProximoToken();
                acumulaRegraSintaticaReconhecida("<X> ::= <variavel>");
                regraSemantica(11);
                break;
            case T_NUMERO:
                buscaProximoToken();
                acumulaRegraSintaticaReconhecida("<X> ::= [0-9]+('.'[0-9]+)");
                regraSemantica(12);
                break;
            case T_ABRE_PARENTESES: {
                buscaProximoToken();
                expr();
                if (token == T_FECHA_PARENTESES) {
                    buscaProximoToken();
                    acumulaRegraSintaticaReconhecida("<X> ::= '(' <expr> ')'");
                } else {
                    registraErroSintatico("Erro Sintatico na linha: " + linhaAtual
                            + "\nReconhecido ao atingir a coluna: " + colunaAtual + "\nLinha do Erro: <" + linhaFonte
                            + ">\n')' esperado mas encontrei: " + lexema);
                }
                regraSemantica(13);
            }
                break;
            default:
                registraErroSintatico("Erro Sintatico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: "
                        + colunaAtual + "\nLinha do Erro: <" + linhaFonte + ">\nFator invalido: encontrei: " + lexema);
        }
    }

    static void fechaFonte() throws IOException {
        rdFonte.close();
    }

    static void movelookAhead() throws IOException {

        if ((ponteiro + 1) > linhaFonte.length()) {

            linhaAtual++;
            ponteiro = 0;

            if ((linhaFonte = rdFonte.readLine()) == null) {
                lookAhead = FIM_ARQUIVO;
            } else {

                StringBuffer sbLinhaFonte = new StringBuffer(linhaFonte);
                sbLinhaFonte.append('\13').append('\10');
                linhaFonte = sbLinhaFonte.toString();

                lookAhead = linhaFonte.charAt(ponteiro);
            }
        } else {
            lookAhead = linhaFonte.charAt(ponteiro);
        }

        // Se comentar esse if, eu terei uma linguagem
        // que diferencia minusculas de maiusculas
        if ((lookAhead >= 'a')
                && (lookAhead <= 'z')) {
            lookAhead = (char) (lookAhead - 'a' + 'A');
        }

        ponteiro++;
        colunaAtual = ponteiro + 1;
    }

    static void buscaProximoToken() throws IOException, ErroLexicoException {
        // int i, j;

        if (lexema != null) {
            ultimoLexema = new String(lexema);
        }
        StringBuffer sbLexema = new StringBuffer("");

        // Salto espaçoes enters e tabs até o inicio do proximo token
        while ((lookAhead == 9)
                || (lookAhead == '\n')
                || (lookAhead == 8)
                || (lookAhead == 11)
                || (lookAhead == 12)
                || (lookAhead == '\r')
                || (lookAhead == 32)) {
            movelookAhead();
        }

        /*--------------------------------------------------------------*
         * Caso o primeiro caracter seja alfabetico, procuro capturar a *
         * sequencia de caracteres que se segue a ele e classifica-la   *
         *--------------------------------------------------------------*/
        if ((lookAhead >= 'A') && (lookAhead <= 'Z')) {
            sbLexema.append(lookAhead);
            movelookAhead();

            while (((lookAhead >= 'A') && (lookAhead <= 'Z'))
                    || ((lookAhead >= '0') && (lookAhead <= '9')) || (lookAhead == '_')) {
                sbLexema.append(lookAhead);
                movelookAhead();
            }

            lexema = sbLexema.toString();

            /* Classifico o meu token como palavra reservada ou id */
            if (lexema.equals("PROGRAM")) {
                token = T_PROGRAMA;
            } else if (lexema.equals("END")) {
                token = T_FIM;
            } else if (lexema.equals("DECLARE")) {
                token = T_DECLARA;
            } else if (lexema.equals("IF")) {
                token = T_IF;
            } else if (lexema.equals("ELSE")) {
                token = T_ELSE;
            } else if (lexema.equals("ENDIF")) {
                token = T_ENDIF;
            } else if (lexema.equals("THEN")) {
                token = T_THEN;
            } else if (lexema.equals("WHILE")) {
                token = T_WHILE;
            } else if (lexema.equals("DO")) {
                token = T_DO;
            } else if (lexema.equals("WRITE")) {
                token = T_WRITE;
            } else if (lexema.equals("READ")) {
                token = T_READ;
            } else if (lexema.equals("BEGIN")) {
                token = T_INICIO;
            } else {
                token = T_IDENTIFICADOR;
            }
        } else if ((lookAhead >= '0') && (lookAhead <= '9')) {
            sbLexema.append(lookAhead);
            movelookAhead();
            while ((lookAhead >= '0') && (lookAhead <= '9')) {
                sbLexema.append(lookAhead);
                movelookAhead();
            }
            token = T_NUMERO;
        } else if (lookAhead == '(') {
            sbLexema.append(lookAhead);
            token = T_ABRE_PARENTESES;
            movelookAhead();
        } else if (lookAhead == ')') {
            sbLexema.append(lookAhead);
            token = T_FECHA_PARENTESES;
            movelookAhead();
        } else if (lookAhead == '{') {
            sbLexema.append(lookAhead);
            token = T_ABRE_CHAVES;
            movelookAhead();
        } else if (lookAhead == '}') {
            sbLexema.append(lookAhead);
            token = T_FECHA_CHAVES;
            movelookAhead();
        } else if (lookAhead == ';') {
            sbLexema.append(lookAhead);
            token = T_PONTO_VIRGULA;
            movelookAhead();
        } else if (lookAhead == ',') {
            sbLexema.append(lookAhead);
            token = T_VIRGULA;
            movelookAhead();
        } else if (lookAhead == '+') {
            sbLexema.append(lookAhead);
            token = T_MAIS;
            movelookAhead();
        } else if (lookAhead == '-') {
            sbLexema.append(lookAhead);
            token = T_MENOS;
            movelookAhead();
        } else if (lookAhead == '*') {
            sbLexema.append(lookAhead);
            movelookAhead();
            if (lookAhead == '*') {
                sbLexema.append(lookAhead);
                movelookAhead();
                token = T_ELEVADO;
            } else {
                token = T_VEZES;
            }
        } else if (lookAhead == '/') {
            sbLexema.append(lookAhead);
            token = T_DIVIDIDO;
            movelookAhead();
        } else if (lookAhead == '%') {
            sbLexema.append(lookAhead);
            token = T_RESTO;
            movelookAhead();
        } else if (lookAhead == '<') {
            sbLexema.append(lookAhead);
            movelookAhead();
            if (lookAhead == '>') {
                sbLexema.append(lookAhead);
                movelookAhead();
                token = T_DIFERENTE;
            } else if (lookAhead == '=') {
                sbLexema.append(lookAhead);
                movelookAhead();
                token = T_MENOR_IGUAL;
            } else {
                token = T_MENOR;
            }
        } else if (lookAhead == '>') {
            sbLexema.append(lookAhead);
            movelookAhead();
            if (lookAhead == '=') {
                sbLexema.append(lookAhead);
                movelookAhead();
                token = T_MAIOR_IGUAL;
            } else {
                token = T_MAIOR;
            }
        } else if (lookAhead == '=') {
            sbLexema.append(lookAhead);
            movelookAhead();
            if (lookAhead == '=') {
                sbLexema.append(lookAhead);
                movelookAhead();
                token = T_IGUAL;
            }
        } else if (lookAhead == ':') {
            sbLexema.append(lookAhead);
            movelookAhead();
            if (lookAhead == '=') {
                sbLexema.append(lookAhead);
                movelookAhead();
                token = T_ATRIBUICAO;
            }
        } else if (lookAhead == FIM_ARQUIVO) {
            token = T_FIM_FONTE;
        } else {
            token = T_ERRO_LEX;
            sbLexema.append(lookAhead);
        }

        lexema = sbLexema.toString();

        mostraToken();

        if (token == T_ERRO_LEX) {
            mensagemDeErro = "Erro Léxico na linha: " + linhaAtual + "\nReconhecido ao atingir a coluna: " + colunaAtual
                    + "\nLinha do Erro: <" + linhaFonte + ">\nToken desconhecido: " + lexema;
            throw new ErroLexicoException(mensagemDeErro);
        }
    }

    static void mostraToken() {

        StringBuffer tokenLexema = new StringBuffer("");

        switch (token) {
            case T_PROGRAMA:
                tokenLexema.append("T_PROGRAMA");
                break;
            case T_ABRE_CHAVES:
                tokenLexema.append("T_ABRE_CHAVES");
                break;
            case T_FECHA_CHAVES:
                tokenLexema.append("T_FECHA_CHAVES");
                break;
            case T_FIM:
                tokenLexema.append("T_FIM");
                break;
            case T_INICIO:
                tokenLexema.append("T_INICIO");
                break;
            case T_DECLARA:
                tokenLexema.append("T_DECLARA");
                break;
            case T_PONTO_VIRGULA:
                tokenLexema.append("T_PONTO_VIRGULA");
                break;
            case T_IDENTIFICADOR:
                tokenLexema.append("T_IDENTIFICADOR");
                break;
            case T_VIRGULA:
                tokenLexema.append("T_VIRGULA");
                break;
            case T_ATRIBUICAO:
                tokenLexema.append("T_ATRIBUICAO");
                break;
            case T_IF:
                tokenLexema.append("T_IF");
                break;
            case T_THEN:
                tokenLexema.append("T_THEN");
                break;
            case T_ENDIF:
                tokenLexema.append("T_ENDIF");
                break;
            case T_ELSE:
                tokenLexema.append("T_ELSE");
                break;
            case T_READ:
                tokenLexema.append("T_READ");
                break;
            case T_ABRE_PARENTESES:
                tokenLexema.append("T_ABRE_PARENTESES");
                break;
            case T_FECHA_PARENTESES:
                tokenLexema.append("T_FECHA_PARENTESES");
                break;
            case T_WRITE:
                tokenLexema.append("T_WRITE");
                break;
            case T_WHILE:
                tokenLexema.append("T_WHILE");
                break;
            case T_DO:
                tokenLexema.append("T_DO");
                break;
            case T_MAIOR:
                tokenLexema.append("T_MAIOR");
                break;
            case T_MAIOR_IGUAL:
                tokenLexema.append("T_MAIOR_IGUAL");
                break;
            case T_DIFERENTE:
                tokenLexema.append("T_DIFERENTE");
                break;
            case T_MENOR_IGUAL:
                tokenLexema.append("T_MENOR_IGUAL");
                break;
            case T_MENOR:
                tokenLexema.append("T_MENOR");
                break;
            case T_IGUAL:
                tokenLexema.append("T_IGUAL");
                break;
            case T_MAIS:
                tokenLexema.append("T_MAIS");
                break;
            case T_MENOS:
                tokenLexema.append("T_MENOS");
                break;
            case T_VEZES:
                tokenLexema.append("T_VEZES");
                break;
            case T_DIVIDIDO:
                tokenLexema.append("T_DIVIDIDO");
                break;
            case T_RESTO:
                tokenLexema.append("T_RESTO");
                break;
            case T_ELEVADO:
                tokenLexema.append("T_ELEVADO");
                break;
            case T_NUMERO:
                tokenLexema.append("T_NUMERO");
                break;

            case T_FIM_FONTE:
                tokenLexema.append("T_FIM_FONTE");
                break;
            case T_ERRO_LEX:
                tokenLexema.append("T_ERRO_LEX");
                break;
            case T_NULO:
                tokenLexema.append("T_NULO");
                break;
            default:
                tokenLexema.append("N/A");
                break;
        }
        System.out.println(tokenLexema.toString() + " ( " + lexema + " )");
        acumulaToken(tokenLexema.toString() + " ( " + lexema + " )");
        tokenLexema.append(lexema);
    }

    private static void abreArquivo() {

        JFileChooser fileChooser = new JFileChooser();

        fileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);

        FiltroSab filtro = new FiltroSab();

        fileChooser.addChoosableFileFilter(filtro);
        int result = fileChooser.showOpenDialog(null);

        if (result == JFileChooser.CANCEL_OPTION) {
            return;
        }

        arqFonte = fileChooser.getSelectedFile();
        abreFonte(arqFonte);

    }

    private static boolean abreFonte(File fileName) {

        if (arqFonte == null || fileName.getName().trim().equals("")) {
            JOptionPane.showMessageDialog(null, "Nome de Arquivo Invalido", "Nome de Arquivo Invalido",
                    JOptionPane.ERROR_MESSAGE);
            return false;
        } else {
            linhaAtual = 1;
            try {
                FileReader fr = new FileReader(arqFonte);
                rdFonte = new BufferedReader(fr);
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
            return true;
        }
    }

    private static void abreDestino() {

        JFileChooser fileChooserLex = new JFileChooser();
        JFileChooser fileChooserSem = new JFileChooser();

        fileChooserLex.setFileSelectionMode(JFileChooser.FILES_ONLY);
        fileChooserSem.setFileSelectionMode(JFileChooser.FILES_ONLY);

        FiltroSab filtroLex = new FiltroSab();
        FiltroSab filtroSem = new FiltroSab();

        fileChooserLex.addChoosableFileFilter(filtroLex);
        fileChooserSem.addChoosableFileFilter(filtroSem);

        int resultLex = fileChooserLex.showSaveDialog(null);
        int resultSem = fileChooserSem.showSaveDialog(null);

        if (resultLex == JFileChooser.CANCEL_OPTION) {
            return;
        }

        if (resultSem == JFileChooser.CANCEL_OPTION) {
            return;
        }

        arqDestinoLex = fileChooserLex.getSelectedFile();
        arqDestinoSem = fileChooserSem.getSelectedFile();

    }

    private static boolean gravaSaida(File fileName) {

        if (arqDestinoLex == null && arqDestinoSem == null || fileName.getName().trim().equals("")) {
            JOptionPane.showMessageDialog(null, "Nome de Arquivo Invalido", "Nome de Arquivo Invalido",
                    JOptionPane.ERROR_MESSAGE);
            return false;
        } else {
            FileWriter fwLex;
            try {
                System.out.println(arqDestinoLex.toString());
                System.out.println(tokensIdentificados.toString());
                fwLex = new FileWriter(arqDestinoLex);
                BufferedWriter bfwLex = new BufferedWriter(fwLex);
                bfwLex.write(tokensIdentificados.toString());
                bfwLex.write(regrasReconhecidas.toString());
                bfwLex.close();
                JOptionPane.showMessageDialog(null, "Arquivo Salvo: " + arqDestinoLex, "Salvando Arquivo",
                        JOptionPane.INFORMATION_MESSAGE);
            } catch (IOException e) {
                JOptionPane.showMessageDialog(null, e.getMessage(), "Erro de Entrada/Saída Léxico",
                        JOptionPane.ERROR_MESSAGE);
            }
            FileWriter fwSem;
            try {
                fwSem = new FileWriter(arqDestinoSem);
                BufferedWriter bfwSem = new BufferedWriter(fwSem);
                bfwSem.write(codigoPascal.toString());
                bfwSem.close();
                JOptionPane.showMessageDialog(null, "Arquivo Salvo: " + arqDestinoSem, "Salvando Arquivo",
                        JOptionPane.INFORMATION_MESSAGE);
            } catch (IOException e) {
                JOptionPane.showMessageDialog(null, e.getMessage(), "Erro de Entrada/Saida Semantico",
                        JOptionPane.ERROR_MESSAGE);
            }
            return true;
        }
    }

    public static void exibeTokens() {

        JTextArea texto = new JTextArea();
        texto.append(tokensIdentificados.toString());
        JOptionPane.showMessageDialog(null, texto, "Tokens Identificados (token/lexema)",
                JOptionPane.INFORMATION_MESSAGE);
    }

    public static void acumulaRegraSintaticaReconhecida(String regra) {

        regrasReconhecidas.append(regra);
        regrasReconhecidas.append("\n");

    }

    public static void acumulaToken(String tokenIdentificado) {

        tokensIdentificados.append(tokenIdentificado);
        tokensIdentificados.append("\n");

    }

    public static void exibeSaida() {

        JTextArea texto = new JTextArea();
        texto.append(tokensIdentificados.toString());
        JOptionPane.showMessageDialog(null, texto, "Analise Lexica", JOptionPane.INFORMATION_MESSAGE);

        texto.setText(regrasReconhecidas.toString());
        texto.append("\n\nStatus da Compilacao:\n\n");
        texto.append(mensagemDeErro);

        JOptionPane.showMessageDialog(null, texto, "Resumo da Compilacao", JOptionPane.INFORMATION_MESSAGE);
    }

    static void registraErroSintatico(String msg) throws ErroSintaticoException {
        if (estadoCompilacao == E_SEM_ERROS) {
            estadoCompilacao = E_ERRO_SINTATICO;
            mensagemDeErro = msg;
        }
        throw new ErroSintaticoException(msg);

    }

    /**
     * Função para montar arquivo linguagem
     **/
    private static void regraSemantica(int numeroRegra) throws ErroSemanticoException {
        System.out.println("Regra Semantica " + numeroRegra);

        switch (numeroRegra) {
            case 0:
                codigoPascal.append("\nprograma codigoPascal;\n");
                break;
            case 1:
                codigoPascal.append("Var ");
                break;
            case 2:
                insereNaTabelaSimbolos(ultimoLexema);
                codigoPascal.append(ultimoLexema + " ");
                break;
            case 3:
                // nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                System.out.println(nodo_1.getCodigo());
                // System.out.println("Codigo 2 " + nodo_2.getCodigo());
                // codigoPascal.append(tabulacao(nivelIdentacao));
                codigoPascal.append(" = " + nodo_1.getCodigoMinusculo());
                break;
            case 4:
                if (VeSeExisteNaTabelaSimbolos(ultimoLexema)) {
                    pilhaSemantica.push(ultimoLexema, 4);
                }
                break;
            case 5:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + "+" + nodo_2.getCodigoMinusculo() + ";\n", 5);
                break;
            case 6:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + "-" + nodo_2.getCodigoMinusculo() + ";\n", 6);
                break;
            case 7:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + "*" + nodo_2.getCodigoMinusculo(), 7);
                break;
            case 8:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + "/" + nodo_2.getCodigoMinusculo(), 8);
                break;
            case 9:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + "%" + nodo_2.getCodigoMinusculo(), 9);
                break;
            case 10:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + "**" + nodo_2.getCodigoMinusculo(), 10);
                break;
            case 11:
                if (VeSeExisteNaTabelaSimbolos(ultimoLexema)) {
                    pilhaSemantica.push(ultimoLexema, 11);
                }
                break;
            case 12:
                pilhaSemantica.push(ultimoLexema, 12);
                break;
            case 13:
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push("(" + nodo_1.getCodigoMinusculo() + ")", 13);
                break;
            case 14:
                nodo_1 = pilhaSemantica.pop();
                codigoPascal.append(tabulacao(nivelIdentacao));
                codigoPascal.append("write( 'Informe a variavel "
                        + nodo_1.getCodigoMinusculo() + " ');\n");
                codigoPascal.append(tabulacao(nivelIdentacao));
                codigoPascal.append("readln(" + nodo_1.getCodigoMinusculo() + ")");
                break;
            case 15:
                nodo_1 = pilhaSemantica.pop();
                if (isDoWhile)
                    nivelIdentacao++;
                codigoPascal.append(tabulacao(nivelIdentacao));
                codigoPascal.append("while ( " + nodo_1.getCodigoMinusculo() + " )\n");
                if (isDoWhile) {
                    nivelIdentacao--;
                } else {
                    nivelIdentacao++;
                }
                break;
            case 16:
                nivelIdentacao--;
                break;
            case 17:
                nodo_1 = pilhaSemantica.pop();
                codigoPascal.append(tabulacao(nivelIdentacao));
                codigoPascal.append("if " + nodo_1.getCodigoMinusculo() + " then\n");
                nivelIdentacao++;
                break;
            case 18:
                nivelIdentacao++;
                break;
            case 19:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + " > " + nodo_2.getCodigoMinusculo(), 19);
                break;
            case 20:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + " < " + nodo_2.getCodigoMinusculo(), 20);
                break;
            case 21:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + " >= " + nodo_2.getCodigoMinusculo(), 21);
                break;
            case 22:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + " <= " + nodo_2.getCodigoMinusculo(), 22);
                break;
            case 23:
                nodo_2 = pilhaSemantica.pop();
                nodo_1 = pilhaSemantica.pop();
                pilhaSemantica.push(nodo_1.getCodigoMinusculo() + " == " + nodo_2.getCodigoMinusculo(), 23);
                break;
            case 25:
                nodo_1 = pilhaSemantica.pop();
                codigoPascal.append(tabulacao(nivelIdentacao));
                codigoPascal
                        .append("write (" + "'" + "Variavel: " + "'" + ", " + nodo_1.getCodigoMinusculo() + ", #"
                                + nodo_1.getCodigoMinusculo().substring(1, nodo_1.getCodigoMinusculo().length())
                                + ")");
                break;
            case 26:
                codigoPascal.append(", ");
                break;
            case 27:
                codigoPascal.append(";\n");
                break;
            case 28:
                codigoPascal.append("begin\n");
                nivelIdentacao++;
                break;
            case 29:
                codigoPascal.append("\nend.");
                break;
            case 30:
                // codigoPascal.append(tabulacao(nivelIdentacao));
                nivelIdentacao--;

                codigoPascal.append(tabulacao(nivelIdentacao) + "end;\n");

                break;
            case 31:
                codigoPascal.append(tabulacao(nivelIdentacao) + "else\n");
                nivelIdentacao++;
                break;
            case 32:
                codigoPascal.append(tabulacao(nivelIdentacao) + "do\n");
                break;
            case 33:
                // insereNaTabelaSimbolos(ultimoLexema);
                codigoPascal.append(tabulacao(nivelIdentacao) + ultimoLexema + " ");
                break;
        }

    }

    private static int buscaTipoNaTabelaSimbolos(String ultimoLexema) throws ErroSemanticoException {
        return tabelaSimbolos.get(ultimoLexema);
    }

    private static boolean VeSeExisteNaTabelaSimbolos(String ultimoLexema) throws ErroSemanticoException {
        if (!tabelaSimbolos.containsKey(ultimoLexema)) {
            throw new ErroSemanticoException("Variavel " + ultimoLexema + " nao esta declarada! linha: " + linhaAtual);
        } else {
            return true;
        }
    }

    private static void insereNaTabelaSimbolos(String ultimoLexema) throws ErroSemanticoException {
        if (tabelaSimbolos.containsKey(ultimoLexema)) {
            throw new ErroSemanticoException("Variavel " + ultimoLexema + " ja declarada! linha: " + linhaAtual);
        } else {
            tabelaSimbolos.put(ultimoLexema, 0);
        }
    }

    static String tabulacao(int qtd) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < qtd; i++) {
            sb.append("    ");
        }
        return sb.toString();
    }
}

/**
 * Classe Interna para criacao de filtro de selecao
 */
class FiltroSab extends FileFilter {

    public boolean accept(File arg0) {
        if (arg0 != null) {
            if (arg0.isDirectory()) {
                return true;
            }
            if (getExtensao(arg0) != null) {
                if (getExtensao(arg0).equalsIgnoreCase("grm")) {
                    return true;
                }
            }
            ;
        }
        return false;
    }

    /**
     * Retorna quais extensoes poderao ser escolhidas
     */
    public String getDescription() {
        return "*.grm";
    }

    /**
     * Retorna a parte com a extensao de um arquivo
     */
    public String getExtensao(File arq) {
        if (arq != null) {
            String filename = arq.getName();
            int i = filename.lastIndexOf('.');
            if (i > 0 && i < filename.length() - 1) {
                return filename.substring(i + 1).toLowerCase();
            }
            ;
        }
        return null;
    }
}