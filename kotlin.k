module KOTLIN-SYNTAX
    import DOMAINS

    // Definição das TAG's
    //seqstrict --> resolve a expressão sequencialmente
    //Bracket --> Resolve precedência desde que informado
    //left --> Resolve da esquerda para a direita
    //strict(x) --> Resolve primeiro a expressão determinada pelo valor de X

    /* === SINTAXE DA LINGUAGEM === */
    syntax Fun ::= "fun main()" "{" Bloco "}"
                | "fun main()" "{" "}"

    syntax Skip ::= "Skip"

    syntax Bloco ::= "{" Statement "}"
                | Statement

    syntax Statement ::= Skip
                    | DeclararVariavel
                    | Assigner
                    | Statement Statement [left]
                    | ExpStrg
                    | ExpArit
                    | ExpAritMod
                    | IfStatement
                    | IfExpression
                    | WhileStatement
                    | DoWhileStatemenet
                    | ForEachStatement
                    | ForKotlin

    syntax FuncDec ::= "function" Id "(" ")" Bloco
                    | "function" Id "(" Params ")" Bloco
    syntax FuncCall ::= Id "(" ")"
    syntax Local ::= "local" "(" Id, Statement ")"
    syntax Params ::= List{Id, ","}
    syntax Values ::= List{Int, ","}

    syntax FuncDecKotlin ::= "fun" Id "(" ")" TipoVar { Bloco }

    syntax TipoVar ::= "Integer" | "Boolean" | "string" | "void"

    syntax Ids ::= List{Id, ","}

    syntax ListValues ::= List{Int, ","}
    syntax ArrayList ::= "[" ListValues "]"

    syntax DeclararVariavel ::= "var" Id ":" TipoVar //corresponde TipoVar Id
                            | "var" Id ":" TipoVar";"
                            | "val" Id ":" TipoVar          
                            | "val" Id ":" TipoVar";"
                            | "var" Id
                            | "val" Id
                            | "var" Id ";"
                            | "val" Id ";"
                            | "var" Ids ":" TipoVar
                            | "val" Ids ":" TipoVar

    syntax Assigner ::= DeclararVariavel "=" ExpArit [strict(2)]
                    | UniqueIdAssigner
                    | DeclararVariavel "=" ExpBool [strict(2)]
                    | DeclararVariavel "=" ExpStrg [strict(2)]

    syntax UniqueIdAssigner ::= Id "=" ExpArit [strict2]
                            | Id "=" ExpBool [strict(2)]
                            | Id "=" ExpStrg [strict(2)]

    syntax ValorVariavel ::= Int | Bool | String

    syntax ExpArit ::= Int
                    | Id
                    > left: ExpArit "*" ExpArit [seqstrict] //precedencia sobre as operações abaixo
                    > left: ExpArit "/" ExpArit [seqstrict]
                    | ExpArit "+" ExpArit [seqstrict]
                    | ExpArit "-" ExpArit [seqstrict]
                    | "(" ExpArit ")" [bracket]

    syntax ExpAritMod ::= Id "++"
                    | Id "--"

    syntax ExpBool ::= Bool
                    | Id
                    | ExpArit ">" ExpArit [strict]
                    | ExpArit ">=" ExpArit [strict]
                    | ExpArit "<" ExpArit [strict]
                    | ExpArit "<=" ExpArit [strict]
                    | ExpArit "==" ExpArit [strict]
                    > "!" ExpBool [seqstrict, left]
                    > left: ExpBool "&&" ExpBool [strict, left]
                    | ExpBool "||" ExpBool [strict, left]
                    | "(" ExpBool ")" [bracket]

    syntax ExpStrg ::= String
                    | Id
                    | ExpStrg "+" ExpStrg
                    | ExpStrg ".equals" ExpStrg

    syntax IfStatement ::= "if" "(" ExpBool ")" Bloco [strict(1)]
                        | "if" "(" ExpBool ")" Bloco ElseIfStatement [strict(1)]

    syntax ElseIfStatement ::= "else if" "(" ExpBool ")" Bloco
                            | "else" Bloco
                            | "else if" "(" ExpBool ")" Bloco ElseIfStatement
    
    syntax IfExpression ::= "if" "(" ExpBool ")" Bloco "else" Bloco [strict(1)]

    syntax WhileStatement ::= "while" "(" ExpBool ")" Bloco

    syntax DoWhileStatemenet ::= "do" Bloco "while" "(" ExpBool ")"

    syntax ForStatement ::= "for" "(" Type UniqueIdAssigner ";" ExpBool ";" ExpAritMod ")" Bloco
    
    syntax ForEachStatement ::= "(" Id "in" "[" ArrayList "]" ")" Bloco

    syntax ForKotlin ::= "for" "(" Type UniqueIdAssigner "in" Int ".." Int ")" Bloco

    /* === REGRAS APENAS DE REESCRITA === */

    //O símbolo => significa reescrita
    rule Skip => .

    rule fun main() { B:Bloco } => B [structural] //regra de programa
    rule fun main() { } => Skip //regra de programa

    rule Stmt1:Statement Stmt2:Statement => Stmt1 ~> Stmt2 [structural] //regra para resolver múltiplos Statement
    rule local (I:Id, Stmt1:Statement Stmt2:Statement) => local(I, Stmt1) ~> local(I, Stmt2) [structural]

    rule V1:ValorVariavel == V2:ValorVariavel => V1 ==K V2
    rule V1:ValorVariavel != V2:ValorVariavel => V1 =/=K V2
    rule ! true  => false
    rule ! false  => true
    rule true && BExp:ExpBool => ExpBool
    rule false && _ => false
    rule true || _ => true
    rule false || BExp:ExpBool => BExp


    rule T:TipoVar .Ids => Skip
    rule T:TipoVar .Ids = _:Int => Skip
    rule foreach (I:Id in [ .ListValues ]) B:Bloco => Skip
    
    rule if (true) { Stmt: Statement } => Stmt //regra para IF igual a true
    rule if (false) { _ } => Skip //regra para IF igual a false
    rule if (true) { B:Bloco } Stmt:ElseIfStatement => B //regra para IF igual a true com else if e/ou else
    rule if (false) { _ } Stmt:ElseIfStatement => Stmt //regra para IF igual a false com else if e/ou else
    rule else if (BExp: ExpBool) { Stmt1:Statement } Stmt2:ElseIfStatement => if (BExp) { Stmt1} Stmt2
    rule else if (BExp: ExpBool) { Stmt:Statement } => if (BExp) {Stmt}
    rule else { Stmt:Statement} => Stmt
    rule if (true) Stmt:Statement else _ => Stmt
    rule if (false) _ else Stmt:Statement => Stmt
    
    rule while (BExp:ExpBool) { Stmt:Statement } => if (BExp) { Stmt while (BExp) { Stmt } } [structural]
    rule do { Stmt:Statement} while (BExp:ExpArit) => Stmt ~> if (BExp) { do { Stmt } while (BExp) } [structural] 
    
    rule for (var I:Id : T:TipoVar = V:ExpArit ; BExp:ExpBool ; AExpMod:ExpAritMod) { Stmt: Statement}
        => I : T = V ~> while (BExp) { Stmt AExpMod } [structural]

    //"for" "(" Type UniqueIdAssigner "in" Int ".." Int ")" Bloco
    //For Kotlin
    rule for ( var I1:Id : T:TipoVar = V:ExpArit in I2:Int .. I3:Int) {Stmt:Statement}
        => I1 : T = V ~> while (I2 < I3) { Stmt }

    /* === REGRAS PARA EXPRESSÕES === */

    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2
    rule I1:Int > I2:Int => I1 >Int I2
    rule I1:Int >= I2:Int => I1 >=Int I2
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2

    rule S1:String + S2:String => S1 +String S2

    /* === REGRAS COM UTILIZACAO DE MEMORIA === */
    
    //Declarar uma variável informando o tipo e sem valor inicial
    rule <k> var I:Id : Integer => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    //Declarar uma variável sem informar o tipo e sem valor inicial
    rule <k> var I:Id : T:TipoVar => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>
    
    //Declarar um conjunto de variaveis sem informar o tipo e sem valor inicial
    rule <k> var (I:Id, Xs Ids) : TipoVar => T Xs ... </k> // I seria o primeiro elemento equanto Xs seriam os demais
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    //Declarar uma variável informando um tipo especifíco e o valor inicial
    rule <k> var I:Id : Integer = V:Int => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var (I:Id, Xs:Ids) : Integer = V:Int => T Xs = V ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id : TipoVar = V:Int => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var (I:Id, Xs:Ids) : TipoVar = V:Int => T Xs = V ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc> 

    rule <k> var I:Id : Boolean = V:Bool => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id : string = V:String => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
    
    rule <k> var I:Id = V:ExpStrg => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        //<types> MTypes:Map => MTypes I |-> String </types>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Bool => L +Int 1 </loc>

    //Atribuir valor a uma variável já declarada

    rule <k> I:Id = V:Int => Skip ... </k>
        <env> ... I |-> L ... </env> //Em qualquer posição que tiver esse ID me retorna o valor da posição de memória
        <store> ... L |-> (_ => V) ... </store> //Onde tiver o L substituir pelo novo valor independente do valor antigo

    rule <k> I1:Id = I2:Id => I1 = V ...</k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V </store>

    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ...</env>
        //<types> ... I |-> String ... </types>
        <store> ... L |-> V ... </store>

    rule <k> I:Id ++ => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>

    rule <k> I:Id -- => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>

    //ForEach
    rule <k> foreach (I:Id in [ (V:Int, Vs:ListValues) ]) {Stmt: Statement} 
            => Stmt ~> foreach (I in [ Vs:ListValues ]) { Stmt } ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
        when notBool (I in keys(MEnv))

    rule <k> foreach (I:Id in [ (V:Int, Vs:ListValues) ]) {Stmt: Statement} 
            => Stmt ~> foreach (I in [ Vs:ListValues ]) { Stmt } 
            ... //Resolve independente do que vier depois
        </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    //Function
    rule <k> thread I:Id ( P:Params ) { Stmt:Statement } => Skip ... </k>
        (.Bag => <thread>
                <id> I </id> //.K pode assumir qualquer tipo
                <scope> Stmt </scope>
                <params> P </params>
                <temp> P </temp>
                <localEnv> .Map </localEnv>
            </thread> 
        )

    rule <k> I:Id (.Values) => local(I, Stmt) ... </k>
        <thread>
            ...
             <id> I </id>
             <scope> Stmt:Statement </scope>
             <params> P </params>
             <temp> ((.Params => P)) </temp>
            ...
        </thread>
    
    rule <k> I:Id ((V:Int, Vs:Values)) => I (Vs) ... </k>
        <thread>
            ...
            <id> I </id>
            <temp> ((P:Id, Ps:Params) => Ps) </temp>
            <localEnv> localMap:Map => localMap P |-> L </localEnv>
            ...
        </thread>
        <store> SMap: Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, var I:Id : Integer = V:Int) => Skip ...  </k>
        <thread>
            ...
             <id> FuncId </id>
             <localEnv> localMap:Map => localMap I |-> L </localEnv>
            ...
        </thread>
        <store> SMap: Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    /* === CONFIGURACAO === */

    configuration <T>
        <k> $PGM:Fun </k> //Definição do programa, todas as computações do programa
        <env> .Map </env> //Mapeamento ID da variavel apontando para a posição de memoria
        <types> .Map </types>
        <store> .Map </store> //Posição de memoria apontando para o valor
        <functions color="orange"> 
            <thread multiplicity="*" color="blue" type="Map">
                <id> .K </id> //.K pode assumir qualquer tipo
                <scope> .K </scope>
                <params> .K </params>
                <temp> .K </temp>
                <localEnv> .Map </localEnv> //Armazena localmente todos os valores ocupando um único espaço de memoria
            </thread>
        </functions> //Cria um novo escopo
        <loc> 1 </loc> //Indica qual a próxima posição de memória
    </T>
 
endmodule

//KResult --> Define quais são os símbolos terminais
module KOTLIN

    import DOMAINS
    import KOTLIN-SYNTAX
    syntax KResult ::= Int | Bool | String

endmodule