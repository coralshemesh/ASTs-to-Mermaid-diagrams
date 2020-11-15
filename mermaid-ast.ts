// <graph> ::= <header> <graphContent> // Graph(dir: Dir, content: GraphContent)
// <header> ::= graph (TD|LR)<newline> // Direction can be TD or LR
// <graphContent> ::= <atomicGraph> | <compoundGraph>
// <atomicGraph> ::= <nodeDecl>
// <compoundGraph> ::= <edge>+
// <edge> ::= <node> --><edgeLabel>? <node><newline> // <edgeLabel> is optional
// // Edge(from: Node, to: Node, label?: string)
// <node> ::= <nodeDecl> | <nodeRef>
// <nodeDecl> ::= <identifier>["<string>"] // NodeDecl(id: string, label: string)
// <nodeRef> ::= <identifier> // NodeRef(id: string)
// <edgeLabel> ::= |<identifier>| // string

export type node = nodeDecl | nodeRef;
export type GraphContent = atomicGraph | compoundGraph;
export type dir = TD | LR;


export interface Graph {tag: "graph", dir: dir, content: GraphContent}
export interface nodeDecl{tag: "nodeDecl",id: string, label: string}
export interface nodeRef{tag: "nodeRef",id: string}
export interface edge{tag: "edge", from: node, to: node, label?:string}
export interface atomicGraph{tag:"atomicGraph", decl: nodeDecl}
export interface compoundGraph{tag:"compoundGraph", edges: edge[]}
export interface TD{tag: "TD"}
export interface LR{tag: "LR"}
export interface edgeLabel{tag: "edgeLable", label: string} //todo check if necessary


export const makeGraph = (dir:dir, content:GraphContent): Graph => ({tag:"graph", dir:dir,content:content});
export const makeNodeDecl= (id:string, label:string):nodeDecl=>({tag: "nodeDecl",id: id, label: label});
export const makeNodeRef = (id: string):nodeRef => ({tag:"nodeRef", id:id});
export const makeEdge = (from:node, to: node, label?:string):edge=>({tag: "edge", from:from, to: to, label:label});
export const makeAtomicGraph = (decl: nodeDecl): atomicGraph => ({tag:"atomicGraph", decl: decl});
export const makeCompoundGraph = (edges: edge[]):compoundGraph => ({tag:"compoundGraph", edges:edges});
export const makeTD = ():TD=>({tag:"TD"});
export const makeLR = ():LR=>({tag:"LR"});
export const makeEdgeLable = (label:string):edgeLabel=>({tag: "edgeLable", label: label});


// Type predicates for disjoint types
export const isGraph = (x: any): x is Graph => x.tag === "Graph";
export const isNodeDecl = (x: any): x is nodeDecl => x.tag === "nodeDecl";
export const isNodeRef = (x: any): x is nodeRef => x.tag === "nodeRef";
export const isEdge = (x: any): x is edge => x.tag === "edge";
export const isAtomicGraph = (x: any): x is atomicGraph => x.tag === "atomicGraph";
export const isCompoundGraph = (x: any): x is compoundGraph => x.tag === "compoundGraph";
export const isTD = (x: any): x is TD => x.tag === "TD";
export const isLR = (x: any): x is LR => x.tag === "LR";
export const isEdgeLabel = (x: any): x is edgeLabel => x.tag === "edgeLabel";//todo check if necessary

// Type predicates for type unions
export const isNode = (x: any): x is node => isNodeDecl(x) || isNodeRef(x);
export const isGraphContent = (x: any): x is GraphContent => isAtomicGraph(x) || isCompoundGraph(x);
export const isDir = (x: any): x is dir => isTD(x) || isLR(x);

