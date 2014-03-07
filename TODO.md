Benchmarks
----------

We should aim at features like the following:

- Check overloaded signatures against implementation. Imagine being able to check all signatures of createElement (provided we have an implementation for it) - not just the last one - which is done now in TypeScript.

```js
createElement(tagName: "div"): HTMLDivElement; 
createElement(tagName: "span"): HTMLSpanElement; 
createElement(tagName: "canvas"): HTMLCanvasElement; 
createElement(tagName: string): HTMLElement;             //  <--- Actually checked by TS 
```

- Verify the logical connection between a specific "tag" field of an object and the functionality of the object itself (where in other languages you would have used a type constructor). This is very pervasive in the TS compiler. E.g.:

```js
[...] if (cur.nodeType() === NodeType.VariableDeclarator) {
  declarationInitASTs[declarationInitASTs.length] = <VariableDeclarator>cur;
}
```

The cast to VariableDeclarator succeeds in TS due to the unsound rule for downcast (for S <: T, if e :: T then <S>e succeeds).

To tackle this soundly, if the general AST node has a type:
```js
{
  _nodetype: number;
  ...
}
```
   
then the VariableDeclarator could have
```js
{
  _nodetype: { number | v = 39};    <----- a unique number that corresponds to NodeType.VariableDeclarator
  ...
}
```

And hence the structural check at the cast should succeed.


- Use of "any" where a union could have been more appropriate (the one we discussed on Monday). Taken from the TS compiler:

```js
private _textOrWidth: any;
public width(): number { return typeof this._textOrWidth === 'number' ? this._textOrWidth : this._textOrWidth.length; }
public text(): string {
  if (typeof this._textOrWidth === 'number') {
    this._textOrWidth = "some string..."; [...]
  }
  return this._textOrWidth;
}
```
    



JS Features
-----------

  - FIELDS
    - definitely missing field

  - METHODS:
    - liquid/pos/objects/meth-00.js

  - DYNAMIC WRITES `e1[e2] = e3` 
    - where: `e2` is a `string`

  - CONSTRUCTORS: 
      What should Array(n) return?  In a setting without strong updates, it 
      returns an array of undefined, but this is not very helpful since it will 
      not be able to be updated to anything useful.

  - CLASSES:
      Nominal or structural subtyping?
      var a /*@ A */ = new A();

      var a /*@ { ... the actual fields of A or less ... } */ = new A();

  - PROTOTYPES:
    - Add formal description of language, translation and discharge of constraints.

  - TRUTHY:
    - Encoding truthy, falsy, undefined, null etc.
      Eg: tc/pos/obj02.js, tc/pos/union05.js


Tool/Implementation
-------------------

  - Add prelude via JSON.

  - Force Class definitions to be at top-level.

  - Add resolved class types to the defined data type environment (tDefs).

  - Add check so that each object field is defined once.

  - Pay attention to capital first letter at function/class defs.

  - Restore the check for unbounded/undefined type variables

  - Multiple fixpoint bindings/invariants in the same environment

  - Disallow type to have multiple tags (if possible)

  - Fix hacky qualifier parse-translation e.g. tests/liquid/pos/arrays/arr-03.js
        
        /* qualif OkLen(v:number, arr:a): v < (len arr) */

    Note use of lower-case which gets translated into tyvars in fixpoint. sigh.

  - There is a confusion with reserved type names (e.g. "null") and defined
    type (any identifier can be considered as a defined type). So it's very easy
    to confuse "null" with "Null". So disallow all types that are not defined
    properly (i.e. through alias, type etc.)

  - Array literal checks are quite slow.
      E.g.: liquid/pos/arrays/arr-07.js

  - Restore the (liquid) property of Array.length (i.e. that it returns a number
    equal to the length of the array)

Failing Tests 
-------------

[ARRAY.LENGTH]
  liquid/pos/lists/safeList.js

[METHODS]
  liquid/pos/objects/meth-00.js

[REGEXP-PARSE]
  liquid/pos/objects/obj-02-parse-bug.js,

[K-VAR INSTANTIATION]
 liquid/pos/lists/safeLists.js,
 liquid/pos/misc/abs-00.js,

[PROTOTYPES - NOT DONE]
 liquid/pos/proto/proto-lookup3.js,
 liquid/pos/proto/proto-lookup4.js,
 liquid/pos/proto/proto-lookup5.js,
 liquid/pos/proto/proto-lookup6.js

