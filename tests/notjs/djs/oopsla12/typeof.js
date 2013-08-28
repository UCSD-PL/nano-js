
/*: typeOf = {(and
  (v :: (value:Ref) / (value: Dict > value.pro) -> {(= v "object")} / same)
  (v :: [A] (value:Ref) / (value: Arr(A) > value.pro) -> {(= v "array")} / same)
  (v :: (value:{(or (= v null) (= (tag v) {"number","boolean","string","undefined"}))})
     -> {(ite (= value null) (= v "null") (= v (tag value)))}))} */ "#type";

var typeOf = function(value) {
  var s = typeof value;
  if (s == 'object') {
    if (value) { return (isArray(value)) ? 'array' : 'object'; }
    else       { return 'null'; }
  }
  return s;
};

//assert (typeOf(1) == "number");
//assert (typeOf("hi") == "string");
//assert (typeOf(true) == "boolean");
//assert (typeOf(null) == "null");
//assert (typeOf({}) == "object");
//assert (typeOf([]) == "array");
//assert (typeOf(undefined) == "undefined");

//typeOf(1);        //notjs == DJS
//typeOf("hi");     //notjs == DJS
//typeOf(true);     //AI: Bool - DJS more precise
//typeOf(null);     //notjs == DJS
//typeOf({});       //AI: value = (StringC(null),Exc((StringC(TypeError)#TrivialDomain_⊥))#TrivialDomain_⊥)) 
//typeOf([]);       //AI: does not support isArray (??)
typeOf(undefined);  //notjs == DJS
