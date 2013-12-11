
///<reference path='../typescript/src/compiler/syntax/syntaxNodes.generated.ts' />
///<reference path='../typescript/src/compiler/syntax/syntaxNode.ts' />
///<reference path='../typescript/src/compiler/syntax/syntaxTree.ts' />
///<reference path='../typescript/src/compiler/syntax/syntaxKind.ts' />
///<reference path='tsdom.ts' />

function endsWith(str: string, suffix : string) {
    return str.indexOf(suffix, str.length - suffix.length) !== -1;
};

class XMLGenerator {

	private _tree : TypeScript.SyntaxTree;
	private _doc : DOMDocument;
	constructor(tree : TypeScript.SyntaxTree){
		this._tree = tree;
		this._start();
		this._end();
	} 

	/**
	 * Create the full CML tree from the source.
	 */
	private _start() : void{
		this._doc = new DOMDocument("DOC");
		this._doc.appendChild(this._toXML(this._tree.sourceUnit()));
	}

	/**
	 * Print the full XML tree.
	 */
	private _end():string{
		console.log(this._doc.toString());
		return this._doc.toString();
	}

	/**
	 * Convert a node of the syntax tree into a XML element, with its
	 * correspondin children or terminal value.
	 */
	private _toXML(el : TypeScript.ISyntaxElement) : DOMElement{
		//Sometimes, el might be null even with a correct program.
		//For example if a type annotation is missing in a variable declaration,
		//the node representing that annotation is null in the tree and therefore
		//it exists (its a child of variabledeclarator), but its a null child. 
		if (el == null) return null;
		
		var name : string = TypeScript.SyntaxKind[el.kind()];
		var res : DOMElement = null;
		if (el.childCount() == 0) {
			res = this._buildLeaf(el);
		} else {
			res = this._buildNode(el);
		}
		return res;
	}

	private _typeKeyword(str: string) : boolean {
		return (str =="AnyKeyword"
			|| str == "BooleanKeyword"
			|| str == "BoolKeyword"
			|| str == "ConstructorKeyword"
			|| str == "DeclareKeyword"
			|| str == "GetKeyword"
			|| str == "ModuleKeyword"
			|| str == "RequireKeyword"
			|| str == "NumberKeyword"
			|| str == "SetKeyword"
			|| str == "StringKeyword"
			|| str == "VoidKeyword")
	}

	/**
	 * Filter: remove all keywords and tokens from the generated xml
	 */
	private _filterLeafs(str : string) : boolean {
		if ((str != "TrueKeyword") 
			&& (str != "FalseKeyword")
			&& (str != "ThisKeyword")
			&& (str != "NullKeyword")
			&& (!this._typeKeyword(str))
			&& (endsWith(str,"Keyword") || endsWith(str,"Token"))){
			return false;
		}
		return true;
	}

	/**
	 * Clean full text: remov all whitespaces,tabs and returns before and after
	 */
	private _cleanFullText(str : string) : string {
		var res : string = "";
		for (var i : number  = 0 ; i < str.length ; i++) {
			var letter = str[i];
			if (letter != ' ' && letter != '\t' && letter != '\r' && letter != '\n')
			res += letter;
		}
		return res;
	}
	/**
	 * This is used to convert the last elements of the SyntaxKind enumeration
	 * into their real value: sometimes they use those values of the enumaration
	 * (which represent the boundaies of the different groups of kinds of nodes
	 * in the enum) instead of using the eal name. So, if you dont convert it you
	 * end up having nodes like <FirstPunctuation>{</FirstPunctuation> instead of
	 *	<OpenBraceToken>{</OpenBraceToken>, wich make much more sense.
	 */
	private _convertNotations(str : string) : string {
		switch (str){
			case "FirstStandardKeyword": return "BreakKeyword";
			case "LastStandardKeyword": return "WithKeyword";
			case "FirstFutureReservedKeyword": return "ClassKeyword";
			case "LastFutureReservedKeyword": return "SuperKeyword";
			case "FirstFutureReservedStrictKeyword": return "ImplementsKeyword";
			case "LastFutureReservedStrictKeyword": return "YieldKeyword";
			case "FirstTypeScriptKeyword": return "AnyKeyword";
			case "LastTypeScriptKeyword": return "StringKeyword";
			case "FirstKeyword": return "FirstStandardKeyword";
			case "LastKeyword": return "LastTypeScriptKeyword";
			case "FirstToken": return "ErrorToken";
			case "LastToken": return "SlashEqualsToken";
			case "FirstPunctuation": return "OpenBraceToken";
			case "LastPunctuation": return "SlashEqualsToken";
			case "FirstFixedWidth": return "FirstKeyword";
			case "LastFixedWidth": return this._convertNotations("LastPunctuation");
			default: return str;
		}
	}

	// In order to get the name of an element of an enum in TS, the syntax is:
	// EnumName[ValueOfEnum], so here TypeScript.SyntaxKind[el.kind()].

	/**
	 * Create a node of the DOM tree based on a node of the syntax tree.
	 */
	private _buildNode(el : TypeScript.ISyntaxElement) : DOMElement {
		var del : DOMElement = new DOMElement(this._convertNotations(TypeScript.SyntaxKind[el.kind()]));
		if (del.tagName() == "ForStatement"){
			return this._buildForNode(del,<TypeScript.ForStatementSyntax>el);
		}
		for (var i = 0 ; i < el.childCount() ; i++){
			del.appendChild(this._toXML(el.childAt(i)))
		}
		return del;
	}

	/**
	 *Special treatment for For loops: we need to identify the four elements of the loop
	 */
	 private _buildForNode (del : DOMElement, el : TypeScript.ForStatementSyntax) : DOMElement {
	 	var tmp : DOMElement = new DOMElement("ForLoopInit");
		tmp.appendChild(this._toXML(el.initializer));
	 	del.appendChild(tmp);
		tmp = new DOMElement("ForLoopTest");
		tmp.appendChild(this._toXML(el.condition));
	 	del.appendChild(tmp);
		tmp = new DOMElement("ForLoopInc");
		tmp.appendChild(this._toXML(el.incrementor));
	 	del.appendChild(tmp)
		tmp = new DOMElement("ForLoopBody");
		tmp.appendChild(this._toXML(el.childAt(9)));
	 	del.appendChild(tmp)
		return del;
	 }

	/**
	 * Create a leaf of the DOM tree based on a leaf of the syntax tree.
	 * The leaf will contain the terminal contained in the syntax tree as 
	 * tst in the XML.
	 */
	private _buildLeaf(el : TypeScript.ISyntaxElement) : DOMElement {
		var name :string = this._convertNotations(TypeScript.SyntaxKind[el.kind()]);
		if (this._filterLeafs(name)) {
			var del : DOMElement = new DOMTextElement(name,this._cleanFullText(el.fullText()));
			return del;
		} else {
			return null;
		}
	}

}