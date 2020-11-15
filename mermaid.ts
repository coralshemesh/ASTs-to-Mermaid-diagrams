import { isLitExp,makeLitExp,isStrExp, isAtomicExp, isLetExp, Binding ,CExp,Parsed,VarDecl, Program,isExp, isProgram, isBoolExp, isNumExp, isVarRef,isVarDecl, isPrimOp, isDefineExp, isProcExp, isIfExp, isAppExp, isCompoundExp, isLetrecExp, isSetExp, makeBoolExp, parseL4, parseL4Exp, Exp} from "./L4-ast"
import { Result, makeOk, makeFailure, mapResult, bind, safe3, safe2, isOk, isFailure } from "../shared/result";
import { map} from "ramda";
import {makeVarGen} from "../L3/substitute"
import { isEmptySExp, isSymbolSExp, isCompoundSExp, SExpValue } from "../part2/L4-value";
import { isNumber, isBoolean, isString } from "../shared/type-predicates";
import { edge, Graph, makeGraph, makeAtomicGraph, makeTD, makeNodeDecl, makeNodeRef, makeCompoundGraph, makeEdge, isAtomicGraph, isCompoundGraph, node, isNodeDecl, isNodeRef, compoundGraph, atomicGraph, nodeDecl } from "./mermaid-ast";
import {parse as p} from "../shared/parser"
import { Sexp } from "s-expression";
//******************     PART 2.2    *********************** */


const makeVarProgram = makeVarGen();
const makeVarDefine = makeVarGen();
const makeVarApp = makeVarGen();
const makeVarProc = makeVarGen();
const makeVarIf = makeVarGen();
const makeVarLet = makeVarGen();
const makeVarLetrec = makeVarGen();
const makeVarSet = makeVarGen();
const makeVarLit = makeVarGen();
const makeVarCompound = makeVarGen();
const makeVarNumber = makeVarGen();
const makeVarBoolean = makeVarGen();
const makeVarString = makeVarGen();
const makeVarSymbol = makeVarGen();
const makeVarEmptySymbol = makeVarGen();
const makeVarNumExp = makeVarGen();
const makeVarBooExp = makeVarGen();
const makeVarPrimOp = makeVarGen();
const makeVarStrExp = makeVarGen();
const makeVarGenRef = makeVarGen();
const makeVarGenDecl = makeVarGen();
const makeVarExp = makeVarGen();
const makeVarRands = makeVarGen();
const makeVarArgs = makeVarGen();
const makeVarBody = makeVarGen();
const makeVarBinding = makeVarGen();
const makeVarBind = makeVarGen();



export const mapL4toMermaid = (exp: Parsed): Result<Graph> =>{

    if (isProgram(exp)){
        return bind (mapResult(mapL4toMermaid,exp.exps),
                    (graphs:Graph[])=> ProgramHandle(graphs));
    }

    else if(isDefineExp(exp)){
        return bind(mapL4toMermaid(exp.val), (x:Graph)=>DefineExpHandle(exp.var, x));
    }

    else if (isAtomicExp(exp)) return getAtomicGraph(exp);

    else if(isCompoundExp(exp)){
        if (isAppExp(exp)){
            return safe2((rator: Graph, rands: Graph[])=> AppExpHandle(rator,rands))
                        (mapL4toMermaid(exp.rator), mapResult(mapL4toMermaid, exp.rands));
        }
        else if(isIfExp(exp)){
            return safe3((test: Graph, then: Graph, alt: Graph) => IfExpHandle(test, then, alt))
                        (mapL4toMermaid(exp.test), mapL4toMermaid(exp.then), mapL4toMermaid(exp.alt));
        }
        else if(isProcExp(exp)){
            return bind(mapResult(mapL4toMermaid, exp.body), (body: Graph[])=> ProcExpHandle(exp.args, body));
        }
        else if(isLetExp(exp)){
            return bind(mapResult(mapL4toMermaid, exp.body),(body:Graph[]) =>LetExpHandle(exp.bindings,body))
        }
        else if(isLetrecExp(exp)){
            return bind(mapResult(mapL4toMermaid, exp.body),(body:Graph[]) =>LetrecExpHandle(exp.bindings,body))
        }
        else if(isSetExp(exp)){
            return safe2((varS: Graph, valS: Graph)=> SetExpHandle(varS,valS))
                         (mapL4toMermaid(exp.var), mapL4toMermaid(exp.val));
        }
        else if(isLitExp(exp)){
            if (isCompoundSExp(exp.val)){
                return safe2((val1: Graph, val2: Graph)=> LitExpHandle(val1,val2))
                            ((handleSExp(exp.val.val1)), handleSExp(exp.val.val2));
            }
            else{
                let GraphEdges: edge[]=[];
                const LitNode = makeNodeRef(makeVarLit("LitExp"));
                if(isEmptySExp(exp.val)){
                    GraphEdges = GraphEdges. concat([makeEdge(LitNode, makeNodeDecl(makeVarEmptySymbol("EmptySExp"), `["EmptySExp"]`), "val")])
                    return makeOk(makeGraph(makeTD(),makeCompoundGraph(GraphEdges)));
                }
                else if(isSymbolSExp(exp.val)){
                    GraphEdges = GraphEdges. concat([makeEdge(LitNode, makeNodeDecl(makeVarSymbol("SymbolSExp"), `["SymbolSExp(${exp.val.val})"]`), "val")])
                    return makeOk(makeGraph(makeTD(),makeCompoundGraph(GraphEdges)));
                } 
                else if(isNumber(exp.val)){
                    GraphEdges = GraphEdges. concat([makeEdge(LitNode, makeNodeDecl(makeVarNumber("number"), `["number(${exp.val})"]`), "val")])
                    return makeOk(makeGraph(makeTD(),makeCompoundGraph(GraphEdges)));
                } 
                else if(isBoolean(exp.val)){
                    GraphEdges = GraphEdges. concat([makeEdge(LitNode, makeNodeDecl(makeVarBoolean("boolean"), `["boolean(${exp.val})"]`), "val")])
                    return makeOk(makeGraph(makeTD(),makeCompoundGraph(GraphEdges)));
                } 
                GraphEdges = GraphEdges. concat([makeEdge(LitNode, makeNodeDecl(makeVarString("string"), `["string(${exp.val})"]`), "val")])
                return makeOk(makeGraph(makeTD(),makeCompoundGraph(GraphEdges)));
            }
        }
    }

return makeFailure("mapL4Mermaid faild in exp " + exp);

}
//************************************************************************************************************

//************************************************************************************************************
export const CompoundSExpHandle = (val1:Graph, val2:Graph):Result<Graph> => {
    let GraphEdges: edge[]=[];
    const CompoundNode = makeNodeRef(makeVarCompound("CompoundSExp"));
    if(isAtomicGraph(val1.content)) GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, val1.content.decl, "val1")]);
    else if(isCompoundGraph(val1.content)){
        GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, refToDecl(val1.content.edges[0].from), "val1")]);
        GraphEdges = GraphEdges.concat(val1.content.edges); //add to graphEdges array all test former edges
    }
    if(isAtomicGraph(val2.content)) GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, val2.content.decl, "val2")]);
    else if(isCompoundGraph(val2.content)){
        GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, refToDecl(val2.content.edges[0].from), "val2")]);
        GraphEdges = GraphEdges.concat(val2.content.edges); //add to graphEdges array all test former edges
    }
    return makeOk(makeGraph(makeTD(), makeCompoundGraph(GraphEdges)));
}

//************************************************************************************************************
export const handleSExp = (val1:SExpValue): Result<Graph> =>
    isCompoundSExp(val1)? safe2((val11: Graph, val21: Graph)=> CompoundSExpHandle(val11,val21))
                                ((handleSExp(val1.val1)), handleSExp(val1.val2)):
    isEmptySExp(val1)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarEmptySymbol("EmptySExp"), `["EmptySExp"]`)))):
    isSymbolSExp(val1)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarSymbol("SymbolSExp"), `["SymbolSExp(${val1.val})"]`)))):
    isNumber(val1)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarNumber("number"), `["number(${val1})"]`)))):
    isBoolean(val1)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarBoolean("boolean"), `["boolean(${val1})"]`)))):
    makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarString("string"), `["string(${val1})"]`))));

//************************************************************************************************************
export const DefineExpHandle = (varD: VarDecl, val: Graph): Result<Graph>=>{
    let GraphEdges: edge[]=[];

    const DefineNode = makeNodeRef(makeVarDefine("DefineExp"));
    const varDeclGraph:Graph= VarDeclHandle(varD);

    GraphEdges = GraphEdges.concat([makeEdgeNodeGraph(DefineNode, varDeclGraph, "var")]);
    GraphEdges = GraphEdges.concat([makeEdgeNodeGraph(DefineNode, val, "val")]);
    if(isCompoundGraph(val.content)) GraphEdges = concatGraphEdges(val.content, GraphEdges); //if val is compound graph add his edges to the global define graph
    return makeOk(makeGraph(makeTD(), makeCompoundGraph(GraphEdges)));
}
//************************************************************************************************************
export const ProgramHandle = (graphs: Graph[]):Result<Graph>=>{
    let GraphEdges: edge[]=[];
    const ProgramNode = makeNodeDecl(makeVarProgram("Program"),`[Program]`);
    const dotsNodeExps = makeNodeDecl(makeVarExp("Exps"),`[:]`);
    GraphEdges = GraphEdges. concat([makeEdge(ProgramNode, dotsNodeExps, "exps")]);
    GraphEdges = GraphEdges.concat(graphs.map(function(x:Graph){return makeEdgeNodeGraph(makeNodeRef(dotsNodeExps.id), x,"");})); //make edges between AppNode and all his children
    graphs.map(function(x:Graph){ if(isCompoundGraph(x.content)) return GraphEdges = concatGraphEdges(x.content, GraphEdges) ;}) //add to graphEdges array all the former edges from graphs

    return makeOk(makeGraph(makeTD(), makeCompoundGraph(GraphEdges)));
}
//************************************************************************************************************
export const LitExpHandle = (val1:Graph, val2:Graph):Result<Graph> => {
    let GraphEdges: edge[]=[];
    const LitNode = makeNodeRef(makeVarLit("LitExp"));
    const CompoundNode = makeNodeRef(makeVarCompound("CompoundSExp"));
    GraphEdges = GraphEdges. concat([makeEdge(LitNode, refToDecl(CompoundNode), "val")]);
    if(isAtomicGraph(val1.content)) GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, val1.content.decl, "val1")]);
    else if(isCompoundGraph(val1.content)){
        GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, refToDecl(val1.content.edges[0].from), "val1")]);
        GraphEdges = GraphEdges.concat(val1.content.edges); //add to graphEdges array all test former edges
    }
    if(isAtomicGraph(val2.content)) GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, val2.content.decl, "val2")]);
    else if(isCompoundGraph(val2.content)){
        GraphEdges = GraphEdges.concat([makeEdge(CompoundNode, refToDecl(val2.content.edges[0].from), "val2")]);
        GraphEdges = GraphEdges.concat(val2.content.edges); //add to graphEdges array all test former edges
    }
    return makeOk(makeGraph(makeTD(), makeCompoundGraph(GraphEdges)));
}

//************************************************************************************************************
export const SetExpHandle = (varS: Graph, valS: Graph):Result<Graph>=>{
    let GraphEdges: edge[]=[];
    const SetNode = makeNodeRef(makeVarSet("SetExp"));
    if(isAtomicGraph(varS.content)) GraphEdges = GraphEdges.concat([makeEdge(SetNode, varS.content.decl, "var")]);
    else if(isCompoundGraph(varS.content)){
        GraphEdges = GraphEdges.concat([makeEdge(SetNode,refToDecl(varS.content.edges[0].from), "var")]);
        GraphEdges = GraphEdges.concat(varS.content.edges); //add to graphEdges array all test former edges
    }
    if(isAtomicGraph(valS.content)) GraphEdges = GraphEdges.concat([makeEdge(SetNode, valS.content.decl, "val")]);
    else if(isCompoundGraph(valS.content)){
        GraphEdges = GraphEdges.concat([makeEdge(SetNode, refToDecl(valS.content.edges[0].from), "val")]);
        GraphEdges = GraphEdges.concat(valS.content.edges); //add to graphEdges array all test former edges
    }
    return makeOk(makeGraph(makeTD(), makeCompoundGraph(GraphEdges)));
}

//************************************************************************************************************
export const LetrecExpHandle = (bindings: Binding[], body: Graph[]): Result<Graph> => {
    let graphEdges: edge[]=[];
    const LetrecNode = makeNodeRef(makeVarLetrec("LetrecExp"));
    const dotsNodeBody = makeNodeDecl(makeVarBody("Body"),`[:]`);
    const dotsNodeBindinds = makeNodeDecl(makeVarBinding("Bindings"),`[:]`);

    graphEdges = graphEdges.concat([makeEdge(LetrecNode, dotsNodeBindinds, "bindings")]);
    graphEdges = graphEdges.concat([makeEdge(LetrecNode, dotsNodeBody, "body")]);

    bindings.map(function(x:Binding){
        const newBind: node = makeNodeRef(makeVarBind("Binding"))
        graphEdges = graphEdges. concat([makeEdge(makeNodeRef(dotsNodeBindinds.id), refToDecl(newBind), "")])
        const VarNode : Graph = VarDeclHandle(x.var)
        graphEdges = graphEdges.concat(makeEdgeNodeGraph(newBind, VarNode,"var"));
        const ValNode :Result<Graph> = mapL4toMermaid(x.val);
        if(isOk(ValNode)) {
            graphEdges= graphEdges.concat([makeEdgeNodeGraph(newBind,ValNode.value,"val")])
            if (isCompoundGraph (ValNode.value.content)) graphEdges =concatGraphEdges(ValNode.value.content, graphEdges)
        }
        else console.log("wrong val in let exp")
    }) ;

    graphEdges = graphEdges.concat(body.map(function(x:Graph){return makeEdgeNodeGraph(makeNodeRef(dotsNodeBody.id), x,"");})) ;
    
    body.map(function(x:Graph){ if(isCompoundGraph(x.content)) return graphEdges =concatGraphEdges(x.content, graphEdges) ;}) //add to graphEdges array all the graphs edges from body array

    return makeOk(makeGraph(makeTD(),makeCompoundGraph(graphEdges)));
}

//************************************************************************************************************
export const LetExpHandle = (bindings: Binding[], body: Graph[]): Result<Graph> => {
    let graphEdges: edge[]=[];
    const LetNode = makeNodeRef(makeVarLet("LetExp"));
    const dotsNodeBody = makeNodeDecl(makeVarBody("Body"),`[:]`);
    const dotsNodeBindinds = makeNodeDecl(makeVarBinding("Bindings"),`[:]`);
    graphEdges = graphEdges.concat([makeEdge(LetNode, dotsNodeBindinds, "bindings")]);
    graphEdges = graphEdges.concat([makeEdge(LetNode, dotsNodeBody, "body")]);

    bindings.map(function(x:Binding){
        const newBind: node = makeNodeRef(makeVarBind("Binding"))
        graphEdges = graphEdges. concat([makeEdge(makeNodeRef(dotsNodeBindinds.id), refToDecl(newBind), "")])
        const VarNode : Graph = VarDeclHandle(x.var)
        graphEdges = graphEdges.concat(makeEdgeNodeGraph(newBind, VarNode,"var"));
        const ValNode :Result<Graph> = mapL4toMermaid(x.val);
        if(isOk(ValNode)) {
            graphEdges= graphEdges.concat([makeEdgeNodeGraph(newBind,ValNode.value,"val")])
            if (isCompoundGraph (ValNode.value.content)) graphEdges =concatGraphEdges(ValNode.value.content, graphEdges)
        }
        else console.log("wrong val in let exp")
    }) ;

    graphEdges = graphEdges.concat(body.map(function(x:Graph){return makeEdgeNodeGraph(makeNodeRef(dotsNodeBody.id), x,"");})) ;

    body.map(function(x:Graph){ if(isCompoundGraph(x.content)) return graphEdges =concatGraphEdges(x.content, graphEdges) ;}) //add to graphEdges array all the graphs edges from body array

    return makeOk(makeGraph(makeTD(),makeCompoundGraph(graphEdges)));
}

//************************************************************************************************************
export const ProcExpHandle = (args: VarDecl[], body:Graph[]): Result<Graph>=>{
    let graphEdges: edge[]=[];
    const ProcNode = makeNodeRef(makeVarProc("ProcExp"));
    const dotsNodeBody = makeNodeDecl(makeVarBody("Body"),`[:]`);
    const dotsNodeArgs = makeNodeDecl(makeVarArgs("Args"),`[:]`);
    graphEdges = graphEdges.concat([makeEdge(ProcNode, dotsNodeBody, "body")]);
    graphEdges = graphEdges.concat([makeEdge(ProcNode, dotsNodeArgs, "args")]);

    const varDeclArr:Graph[] = map(VarDeclHandle, args);
    graphEdges = graphEdges.concat(varDeclArr.map(function(x:Graph){return makeEdgeNodeGraph(makeNodeRef(dotsNodeArgs.id), x,"");})); //add to graphEdges the new edges between args node to all varDecl nodes
    graphEdges = graphEdges.concat(body.map(function(x:Graph){return makeEdgeNodeGraph(makeNodeRef(dotsNodeBody.id), x,"");})) ;//add to graphEdges the new edges between body node to all body graphs

    body.map(function(x:Graph){ if(isCompoundGraph(x.content)) graphEdges =concatGraphEdges(x.content, graphEdges) ;}) //add to graphEdges array all the former edges

    return makeOk(makeGraph(makeTD(),makeCompoundGraph(graphEdges))); //make big graph from body-graphs and all varDecls
}

//************************************************************************************************************
export const VarDeclHandle = (varD: VarDecl): Graph => 
    makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarGenDecl("VarDecl"),`["VarDecl(${varD.var})"]`)));

//************************************************************************************************************
export const IfExpHandle = (test: Graph, then: Graph, alt: Graph) : Result<Graph> => {
    let graphEdges: edge[]=[];
    const IfNode = makeNodeRef(makeVarIf("IfExp"));
    if(isAtomicGraph(test.content)) graphEdges = graphEdges.concat([makeEdge(IfNode, test.content.decl, "test")]);
    else if(isCompoundGraph(test.content)){
        graphEdges = graphEdges.concat([makeEdge(IfNode, refToDecl(test.content.edges[0].from), "test")]);
        graphEdges = graphEdges.concat(test.content.edges); //add to graphEdges array all test former edges
    } 
    if(isAtomicGraph(then.content)) graphEdges = graphEdges.concat([makeEdge(IfNode, then.content.decl, "then")]);
    else if(isCompoundGraph(then.content)){
        graphEdges = graphEdges.concat([makeEdge(IfNode, refToDecl(then.content.edges[0].from), "then")]);
        graphEdges = graphEdges.concat(then.content.edges); //add to graphEdges array all then former edges
    } 
    if(isAtomicGraph(alt.content)) graphEdges = graphEdges.concat([makeEdge(IfNode, alt.content.decl, "alt")]);
    else if(isCompoundGraph(alt.content)){
        graphEdges = graphEdges.concat([makeEdge(IfNode, refToDecl(alt.content.edges[0].from), "alt")]);
        graphEdges = graphEdges.concat(alt.content.edges); //add to graphEdges array all alt former edges
    } 
   
    return makeOk(makeGraph(makeTD(),makeCompoundGraph(graphEdges))); //make new graph with test&then&alt graphs and the new edges&nodes
}

//************************************************************************************************************
export const AppExpHandle = (rator: Graph, rands: Graph[]) :Result<Graph> =>{
    let graphEdges: edge[]=[];
    const AppNode = makeNodeRef(makeVarApp("AppExp"));
    const dotsNode = makeNodeDecl(makeVarRands("Rands"),`[:]`);

    if(isAtomicGraph(rator.content)){
        graphEdges = graphEdges.concat([makeEdge(AppNode , rator.content.decl, "rator")]);
    }
    else if (isCompoundGraph(rator.content)) {
        graphEdges =graphEdges.concat([makeEdge(AppNode, refToDecl(rator.content.edges[0].from), "rator")]);
        graphEdges =graphEdges.concat(rator.content.edges); //add to graphEdges array all the former edges
    } 
    graphEdges = graphEdges.concat([makeEdge(AppNode, dotsNode, "rands")]);

    graphEdges =graphEdges.concat(rands.map(function(x:Graph){return makeEdgeNodeGraph(makeNodeRef(dotsNode.id), x,"");})); //make edges between AppNode and all rands
    rands.map(function(x:Graph){ if(isCompoundGraph(x.content)) return graphEdges =concatGraphEdges(x.content, graphEdges) ;}) //add to graphEdges array all the former edges

    return makeOk(makeGraph(makeTD(),makeCompoundGraph(graphEdges))); //make new graph with rator & rands graphs and the new edges&nodes
}

//************************************************************************************************************
export const concatGraphEdges = (G : compoundGraph, graphEdges:edge[]):edge[]=> graphEdges.concat(G.edges);

//************************************************************************************************************
export const getAtomicGraph = (exp :Parsed): Result<Graph> =>
    isBoolExp(exp)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarBooExp("BoolExp"),`["BoolExp(${exp.val=== true? "#t": "#f"})"]`)))):
    isNumExp(exp)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarNumExp("NumExp"), `["NumExp(${exp.val})"]`)))):
    isVarRef(exp)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarGenRef("VarRef"), `["VarRef(${exp.var})"]`)))):
    isStrExp(exp)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarStrExp("StrExp"), `["StrExp(${exp.val})"]`)))):
    isPrimOp(exp)? makeOk(makeGraph(makeTD(),makeAtomicGraph(makeNodeDecl(makeVarPrimOp("PrimOp"), `["PrimOp(${exp.op})"]`)))):
    makeFailure("wrong exp");

//************************************************************************************************************
export const makeEdgeNodeGraph = (fromN:node, to: Graph, label?:string):edge =>
    isAtomicGraph(to.content)? makeEdge(fromN, to.content.decl, label):
    isCompoundGraph(to.content) ? makeEdge(fromN, refToDecl(to.content.edges[0].from), label):
    makeEdge(fromN, makeNodeRef("wrong graph"), label); //never get here
//************************************************************************************************************

export const refToDecl = (node:node) : node =>
    isNodeRef(node) ? makeNodeDecl(node.id, `[${refIdToDeclLable(node.id)}]`):
    makeNodeDecl(node.id, "need to be ref but got decl")

//************************************************************************************************************

export const refIdToDeclLable = (RefId : string) : string => {
    if(RefId.includes("ProcExp")) return "ProcExp";
    else if(RefId.includes("AppExp")) return "AppExp";
    else if(RefId.includes("CompoundSExp")) return "CompoundSExp";
    else if(RefId.includes("IfExp")) return "IfExp";
    else if(RefId.includes("LetExp")) return "LetExp";
    else if(RefId.includes("LetrecExp")) return "LetrecExp";
    else if(RefId.includes("Program")) return "Program";
    else if(RefId.includes("LitExp")) return "LitExp";
    else if(RefId.includes("DefineExp")) return "DefineExp";
    else if(RefId.includes("SetExp")) return "SetExp";
    else if(RefId.includes("Binding")) return "Binding"
    return "wrong string";
}


//******************     PART 2.3    *********************** */

export const unparseMermaid = (exp: Graph): Result<string>=>
    bind(unparseMermaid2(exp), (str : string) => makeOk(exp.tag +" "+ exp.dir.tag + '\n'+ str))

 //************************************************************************************************************
export const unparseMermaid2 = (exp:Graph):Result<string> =>
    isAtomicGraph(exp.content) ? atomicToString(exp.content):
    isCompoundGraph(exp.content) ? CompoundToString(exp.content):
    makeFailure("exp is not a graph");

//************************************************************************************************************

export const atomicToString = (atomic : atomicGraph): Result<string> =>
    makeOk(`${atomic.decl.id}${atomic.decl.label}`)

//************************************************************************************************************
 export const CompoundToString =(compGraph: compoundGraph): Result<string> =>{
    return bind(mapResult(edgeToString, compGraph.edges),
                (stringArr:string[])=>makeOk(stringArr.join('\n')))
 }
 //************************************************************************************************************
export const edgeToString = (edge: edge) : Result<string> =>{
    if(isNodeDecl(edge.from)){
        if(isNodeDecl(edge.to))
            if (edge.label !== "") return makeOk(`${edge.from.id}${edge.from.label} -->|${edge.label}| ${edge.to.id}${edge.to.label}`);
            else return makeOk(`${edge.from.id}${edge.from.label} --> ${edge.to.id}${edge.to.label}`);
        else if (isNodeRef(edge.to))
            if(edge.label !== "") return makeOk(`${edge.from.id}${edge.from.label} -->|${edge.label}| ${edge.to.id}`);
            else return makeOk(`${edge.from.id}${edge.from.label} --> ${edge.to.id}`);
    }
    else if (isNodeRef(edge.from)){
            if(isNodeDecl(edge.to))
            if (edge.label !== "") return makeOk(`${edge.from.id} -->|${edge.label}| ${edge.to.id}${edge.to.label}`);
            else return makeOk(`${edge.from.id} --> ${edge.to.id}${edge.to.label}`);
        else if (isNodeRef(edge.to))
        if (edge.label !== "") return makeOk(`${edge.from.id} -->|${edge.label}| ${edge.to.id}`);
        else return makeOk(`${edge.from.id} --> ${edge.to.id}`);
    }
    return makeFailure("edge info is wrong\n");
}

export const L4toMermaid = (concrete: string): Result<string>=>{
    if (!concrete) return makeFailure("empty string");
    const ret : Result<Program> = parseL4(concrete);
    if(isOk(ret)) return bind(mapL4toMermaid(ret.value), (graph:Graph)=>unparseMermaid(graph));
    else if (isFailure(ret) && concrete.startsWith("(L4")) return ret ;
    return bind(bind(bind(bind(p(concrete), (x:Sexp) => parseL4Exp(x)), (exp:Exp)=>mapL4toMermaid(exp)),(graph:Graph)=>firstIsDecl(graph)), (graph2:Graph)=> unparseMermaid(graph2));
}
 

export const firstIsDecl = (graph : Graph) : Result<Graph> => {
    if(isCompoundGraph(graph.content)) {
       const nodeDecl : node = refToDecl(graph.content.edges[0].from)
       const newEdge : edge = makeEdge(nodeDecl,graph.content.edges[0].to, graph.content.edges[0].label)
       let graphArr : edge[] = graph.content.edges.slice(1, graph.content.edges.length)
        graphArr = ([newEdge]).concat(graphArr)
        return makeOk(makeGraph(makeTD(),makeCompoundGraph(graphArr)))
    }
    return makeOk(graph);
}
