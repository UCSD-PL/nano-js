

var tab : string = "    ";

function tabNtimes(n : number) : string{
	if (n == undefined) return "";
	var res : string = "";
	for (var i : number = 0 ; i < n ; i++){
		res += tab;
	}
	return res;
}


class DOMElement {

	private _attrs : DOMAttribute[] = [];
	private _children : DOMElement[] = [];
	private _parent : DOMElement = null; 

	constructor (private _tagName : string){}

	public appendChild(el:DOMElement){
		if (el == null) return;
		if (el._parent != null){
			var index = el._parent._children.indexOf(el);
			el._parent._children.splice(index, 1);
		}
		el._parent = this;
		this._children.push(el);
	}

	public tagName() : string {return this._tagName;}

	public appendAttr(at:DOMAttribute){
		this._attrs.push(at);
	}

	public childCount() : number{
		return this._children.length;
	}

	public childAt(i : number) : DOMElement{
		return this._children[i];
	}

	public attrCount() : number{
		return this._attrs.length;
	}

	public attrAt(i : number) : DOMAttribute{
		return this._attrs[i];
	}

	public toString(tab?: number) : string {
		var str : string = tabNtimes(tab);
		str += "<"+this._tagName;
		for (var i = 0; i < this.attrCount() ; i++ ){
			str += this.attrAt(i).toString();
		}
		if (this.childCount() == 0){
			str += "/>\n";
		} else {
			str += ">\n";
			for (var i = 0; i < this.childCount() ; i++ ){
				str += this.childAt(i).toString(tab+1);
			}
			str += tabNtimes(tab) + "</"+this._tagName+">\n";
		}
		return str;
	}

}

class DOMDocument extends DOMElement{

	public appendChild(el:DOMElement){
		if (this.childCount() > 0){
			return;
		}
		super.appendChild(el);
	}

	public toString(tab?: number) :string {
		if (this.childCount() == 0){
			return "";
		} 
		return this.childAt(0).toString(0);
	}
}

class DOMTextElement extends DOMElement{

	constructor (tagName : string, private _text : string){
		super(tagName);
	}

	public appendChild(el:DOMElement){
		return;
	}

	public toString(tab?: number) :string {
		var str : string = tabNtimes(tab);
		str += "<"+this.tagName();
		for (var i = 0; i < this.attrCount() ; i++ ){
			str += this.attrAt(i).toString();
		}
		if (this.getText() == null || this.getText() == ""){
			str += "/>\n";
		} else {
			str += ">";
			str += this.getText();
			str += "</"+this.tagName()+">\n";
		}
		return str;
	}

	public getText() {return this._text;}
	public setText(str : string) {this._text = str;}

}

class DOMAttribute {
	constructor(private _id : string, private _val :string){}
	public getId():string{return this._id;}
	public getValue():string{return this._val;}
	public toString():string {return " "+this.getId()+"=\""+this.getValue()+"\"";}
}


/*
var doc : DOMDocument = new DOMDocument("DOC");

var el1 : DOMElement = new DOMElement("el1");
var el2 : DOMElement = new DOMElement("el2");
var el3 : DOMElement = new DOMElement("el3");

doc.appendChild(el1);
doc.appendChild(el2);
console.log(doc.childAt(0)==el1);
console.log(doc.childCount()==1);

var el11 : DOMElement = new DOMElement("el11");
var el12 : DOMElement = new DOMElement("el12");

el1.appendChild(el11);
el1.appendChild(el12);
console.log(el1.childCount() == 2);

el2.appendChild(el3);

var tel1 : DOMTextElement = new DOMTextElement("Tel1","text1")

el12.appendChild(tel1);
el12.appendChild(el2);


var attr1 : DOMAttribute = new DOMAttribute("id","1");
var attr2 : DOMAttribute = new DOMAttribute("id","2");
el1.appendAttr(attr1);
console.log(el1.attrCount() == 1);
el11.appendAttr(attr2);
console.log(el11.attrCount() == 1);

console.log(doc.toString());
*/

