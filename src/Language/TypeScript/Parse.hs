module Language.TypeScript.Parse (parseTypeScript) where

import Text.Printf
import System.Environment
import System.IO
import System.FilePath.Posix
import Data.List
import Text.XML.Light
import Text.Regex.Posix
import Language.ECMAScript3.Syntax
import Language.Nano.Typecheck.Types
import Language.Fixpoint.Types as F (Symbol, stringSymbol)
import Language.Fixpoint.Misc (executeShellCommand)



main = do (arg :_) <- getArgs
          pgm      <- parseTypeScript arg
          print pgm


{-TOP LEVEL FUNCTIONS-}

{- 
  Parse TypeScript into a Haskell object.
  Gets the filepath to the .ts file
  Returns the Haskell object representing the source code.
-}
parseTypeScript     :: FilePath -> IO (JavaScript (Maybe Type))
parseTypeScript fts
  = do fxml <- convertTs2XML fts
       parseTypeScriptXML fxml

{-
  Parse TypeScript into an XML file and return the location to that file.
  Gets the filepath to the .ts file.
  Returnsthe filepath to the equivalent XML file.
-}
convertTs2XML        :: FilePath -> IO FilePath
convertTs2XML inFile 
  = do executeShellCommand "ts2xml" convertCommand 
       return outFile
       where
         convertCommand = printf "%s %s > %s" convFile inFile outFile
         convFile       = "$HOME/CSE199/nano-ts/run" 
         outFile        = replaceExtension inFile ".xml"

{-
  Parse an XML file representing a TS code into a Haskell object.
  Gets the filepath to the XML file.
  Returns the Haskell object representing the TS code.
-}
parseTypeScriptXML     :: FilePath -> IO (JavaScript (Maybe Type))
parseTypeScriptXML arg =
  do contents <- readFile arg
     case parseXMLDoc contents of -- returns a Maybe Element
        Nothing     -> error "Failed to parse xml"
        Just rootEl -> return $ xml2script rootEl


{-UTILITIES-}
{-
  Split a string based on a predicate.
-}
split     :: (Char -> Bool) -> String -> [String]
split p s = case dropWhile p s of
               "" -> []
               s' -> w : split p s''
                     where (w, s'') = break p s'

{-
  Remove the quotes around a String.
-}
removeQuotes   :: String -> String
removeQuotes s = if (head s) == '\"' || (head s) == '\'' 
                 then
                  if (last s) == '\"' || (last s) == '\'' 
                    then (tail (init s))
                    else (tail s)
                  else if (last s) == '\"' || (last s) == '\'' then (init s)
                  else s

{-XML MANIPULATION FUNCTIONS-}

{-
  Create a lost of pairs of the folowing form:
  [(Str,El)] where El is a child node of the passed Element in the XML tree
  and Str is the tagname of each El.
  The returned list gives a convenient way to access the inferior levels in
  the XML tree.
-}
createPairs     :: Element -> [(String, Element)]
createPairs el  = [ (qName (elName e), e) | x@(Elem e) <- (elContent el)]

{-
  Given an element and a tagname, find all the elements that are below the 
  given one in the XML tree with that tagname.
-}
getChildByTag        :: Element -> String -> [Element]
getChildByTag el str = let target x = ((fst x) == str) in 
                       map snd (filter target (createPairs el))

{-
  Given an element and a tagname, find the only element that is below the 
  given one in the XML tree with that tagname.
  If there is more than one, an error is raised.
-}
getUChildByTag        :: Element -> String -> Element
getUChildByTag el str = let pairs = getChildByTag el str in
                        if length pairs > 1 
                          then error ("The tag "++qName (elName el)++" should only have one child of tag"++str++".")
                          else pairs!!0

{-
  Given an element and a regular expression in a String, find all the
  elements belowthe givne one that have a tagname matching the regex.
  The returned value is a list of pairs [(Str,El)] where Str is the 
  tagname of each matching element and El is the element itself.
-}
getChildByRegex        :: Element -> String -> [(String,Element)]
getChildByRegex el str = let target x = (((fst x) =~ str)::Bool) in filter target (createPairs el)

{-
  Given an element, it returns its only child in the XML tree.
  The return value is a tuple (Str,El) where Str is the tagname of the
  only child and El is the child itself.
  If the given element has more than one child an error is raised.
-}
getUniqueChild    :: Element -> (String,Element)
getUniqueChild el = let pairs = createPairs el in
                    if length pairs > 1 
                      then error ("The tag "++qName (elName el)++" should only have one child.")
                      else head pairs

{-
  Returns the text contained in an element (i.e. t in <tag>t</tag>)
-}
getText     :: Element -> String
getText el  = concat [ (cdData t) | x@(Text t) <- (elContent el)]

{-CONVERSION FUNTIONS-}

{-
  Take the root element of an XML file as a handle and convert the
  XML file in a Haskell object reprensenting the TS code encoded in XML.
-}
xml2script :: Element -> JavaScript (Maybe (RType ()))
--The top elemen is 'SourceUnit' which has 1 child (List of statements).
xml2script el = Script Nothing  (xml2ListStatement (head (createPairs el)))

{-
  Converts any XML element that represents an statement into a Statement.
  It takes a tuple (Str,El) where Str is the tagname of the XML element 
  to convert and El is the element itself.
-}
xml2Statement :: (String,Element) -> Statement (Maybe (RType ()))
--Block has only one child: a list of statements.
xml2Statement ("Block",elmt) = BlockStmt Nothing (xml2ListStatement (head (getChildByRegex elmt "(.)*List$")))
--ExpressionStatement has one child: the expression itself.
xml2Statement ("ExpressionStatement",elmt) = ExprStmt Nothing (xml2Expression (getUniqueChild elmt))
--EmptyStatement has no children.
xml2Statement ("EmptyStatement",elmt) = EmptyStmt Nothing
--IfStatement has 2 or 3 children: condition, if-true-statement, and optionally if-false-statement
xml2Statement ("IfStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 2 then  --simple if
  IfSingleStmt Nothing (xml2Expression (exprParts!!0)) 
                       (xml2Statement (exprParts!!1)) 
  -- if with else
  else IfStmt Nothing (xml2Expression (exprParts!!0)) 
                      (xml2Statement (exprParts!!1)) 
                      (xml2Statement ("ElseClause",getUChildByTag elmt "ElseClause")) 
--ElseClause can only have one clause (might be a block to contain more than one statement)
xml2Statement ("ElseClause",elmt) = xml2Statement (getUniqueChild elmt)
--ForStatement has four children.
xml2Statement ("ForStatement",elmt) =
  ForStmt Nothing (forInitExpression (getUChildByTag elmt "ForLoopInit"))
                  (forCondExpression (getUChildByTag elmt "ForLoopTest"))
                  (forIncrExpression (getUChildByTag elmt "ForLoopInc"))
                  (xml2Statement $ (createPairs (getUChildByTag elmt "ForLoopBody"))!!0)             
--ForInStatement: three children: the iterator, the iterable and the block
xml2Statement ("ForInStatement",elmt) =
  let pairs = createPairs elmt in
  ForInStmt Nothing (forInInitExpression (snd (pairs!!0)))
                    (xml2Expression (pairs!!1))
                    (xml2Statement (pairs!!2))
--WhileStatement has 2 children: the condition and the body
xml2Statement ("WhileStatement",elmt) = 
  let pairs = createPairs elmt in
  WhileStmt Nothing (xml2Expression (pairs!!0)) (xml2Statement (pairs!!1))
--DoStatement has 2 children (do-while)): the body and the condition
xml2Statement ("DoStatement",elmt) = 
  let pairs = createPairs elmt in
  DoWhileStmt Nothing (xml2Statement (pairs!!0)) (xml2Expression (pairs!!1)) 
--ReturnStatement migh have a child or not.
xml2Statement ("ReturnStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 0 then  ReturnStmt Nothing Nothing --empty return
  else ReturnStmt Nothing (Just (xml2Expression (exprParts!!0)))
--Break/ContinueStatement might contain a label, or nothing.
--If there is a label, its in an IdentfierName tag under the breakstmt, so
--we extract the content from that tag
xml2Statement ("BreakStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 0 then  BreakStmt Nothing Nothing --empty return
  else BreakStmt Nothing (Just (Id Nothing (getText (snd (exprParts!!0)))))
xml2Statement ("ContinueStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 0 then  ContinueStmt Nothing Nothing --empty return
  else ContinueStmt Nothing (Just (Id Nothing (getText (snd (exprParts!!0)))))
--LabeledStatement contains the label itself as  child in a IdentifierName tag
--and a Statement of any kind (only one!)
xml2Statement ("LabeledStatement",elmt) =
  LabelledStmt Nothing (Id Nothing (getText (getUChildByTag elmt "IdentifierName"))) 
                       (xml2Statement $ (createPairs elmt)!!1)
--VaribleStatement contisn a list of modifiers and the variabledeclaration statement wich contains a separatedlist
xml2Statement ("VariableStatement",elmt) = 
  let sepList = snd $ (getChildByRegex (getUChildByTag elmt "VariableDeclaration") "(.)*List$")!!0 in
  VarDeclStmt Nothing (map variableDeclaratorExpression (getChildByTag sepList "VariableDeclarator"))
--SwitchStatement contains the test expression and a list of Case/DefaultSwitchDlause
xml2Statement ("SwitchStatement",elmt) =
  let children = createPairs elmt in 
  SwitchStmt Nothing  (xml2Expression (children!!0)) 
                      (map caseClauseExpression (getChildByRegex (snd $ (getChildByRegex elmt "(.)*List$")!!0) "(.)*SwitchClause"))
--WithStatement 2 children
xml2Statement ("WithStatement",elmt) =
  let children = createPairs elmt in 
  WithStmt Nothing  (xml2Expression (children!!0)) (xml2Statement (children!!1))
--ThrowStatement contains only one child, expression.
xml2Statement ("ThrowStatement",elmt) =
  let children = createPairs elmt in 
  ThrowStmt Nothing  (xml2Expression (children!!0))
--FunctionDeclaration contains modifiers, name,args and body.
xml2Statement ("FunctionDeclaration",elmt) =
  let children = createPairs elmt in
  FunctionStmt (getFunctionType elmt) 
               (Id Nothing(getText $ getUChildByTag elmt "IdentifierName" )) 
               (xml2ListId ("ParameterList",(getUChildByTag (getUChildByTag elmt "CallSignature") "ParameterList"))) 
               [(xml2Statement (children!!3))]
--TryStatement 
xml2Statement ("TryStatement",elmt) = tryCatchFinnalyStatement elmt
--FinallyClause contains only one child
xml2Statement ("FinallyClause",elmt) = xml2Statement $ (createPairs elmt)!!0
--Any other unsupported types
xml2Statement (s,_) = error ("Exception statement: string of type:" ++ s)

{-
  Convert an Element of kind List (see SyntaxKind.ts in the ts compiler) into 
  a list of the statements contained in the list.
-}
xml2ListStatement :: (String,Element) -> [Statement (Maybe (RType ()))]
--List is a generic list of statements.
xml2ListStatement (_,elmt) = (map xml2Statement (createPairs elmt))

{-
  Convert an Element of kind List of expressions (see SyntaxKind.ts in the ts
  compiler) into a list of the expressions contained in the list.
-}
xml2ListExpression :: (String,Element) -> [Expression (Maybe (RType ()))]
--ARgumentList has only one child which is a list
xml2ListExpression ("ArgumentList",elmt) = (xml2ListExpression (getUniqueChild elmt))
--List is a generic list of expressions.
xml2ListExpression (_,elmt) = (map xml2Expression (createPairs elmt))

{-
  Convert an Element of kind List of ID's (see SyntaxKind.ts in the ts
  compiler) into a list of the Id contained in the list.
-}
xml2ListId :: (String,Element) -> [Id (Maybe (RType ()))]
xml2ListId ("ParameterList",elmt) = xml2ListId (getUniqueChild elmt)
xml2ListId (s,elmt) = map xml2Id (createPairs elmt)

{-
  Given an element and its tagname, return the expression representing
  that element as a Haskell object.
-}
xml2Expression :: (String,Element) -> Expression (Maybe (RType ()))
--InfixExpressions:
-- They all have 2 children (left and right oprands).
xml2Expression ("LogicalOrExpression",elmt)                   = infixExpression OpLOr elmt
xml2Expression ("LogicalAndExpression",elmt)                  = infixExpression OpLAnd elmt 
xml2Expression ("BitwiseOrExpression",elmt)                   = infixExpression OpBOr elmt 
xml2Expression ("BitwiseExclusiveOrExpression",elmt)          = infixExpression OpBXor elmt 
xml2Expression ("BitwiseAndExpression",elmt)                  = infixExpression OpBAnd elmt 
xml2Expression ("EqualsWithTypeConversionExpression",elmt)    = infixExpression OpEq elmt 
xml2Expression ("NotEqualsWithTypeConversionExpression",elmt) = infixExpression OpNEq elmt 
xml2Expression ("EqualsExpression",elmt)                      = infixExpression OpStrictEq elmt 
xml2Expression ("NotEqualsExpression",elmt)                   = infixExpression OpStrictNEq elmt  
xml2Expression ("LessThanExpression",elmt)                    = infixExpression OpLT elmt 
xml2Expression ("GreaterThanExpression",elmt)                 = infixExpression OpGT elmt 
xml2Expression ("LessThanOrEqualExpression",elmt)             = infixExpression OpLEq elmt 
xml2Expression ("GreaterThanOrEqualExpression",elmt)          = infixExpression OpGEq elmt 
xml2Expression ("InstanceOfExpression",elmt)                  = infixExpression OpInstanceof elmt 
xml2Expression ("InExpression",elmt)                          = infixExpression OpIn elmt 
xml2Expression ("LeftShiftExpression",elmt)                   = infixExpression OpLShift elmt 
xml2Expression ("SignedRightShiftExpression",elmt)            = infixExpression OpSpRShift elmt 
xml2Expression ("UnsignedRightShiftExpression",elmt)          = infixExpression OpZfRShift elmt 
xml2Expression ("MultiplyExpression",elmt)                    = infixExpression OpMul elmt 
xml2Expression ("DivideExpression",elmt)                      = infixExpression OpDiv elmt 
xml2Expression ("ModuloExpression",elmt)                      = infixExpression OpMod elmt 
xml2Expression ("AddExpression",elmt)                         = infixExpression OpAdd elmt 
xml2Expression ("SubtractExpression",elmt)                    = infixExpression OpSub elmt 
--AssignExpr: two children: the LValue and the right expression.
xml2Expression ("AssignmentExpression",elmt)                  = assignExpression OpAssign elmt
xml2Expression ("AddAssignmentExpression",elmt)               = assignExpression OpAssignAdd elmt
xml2Expression ("SubtractAssignmentExpression",elmt)          = assignExpression OpAssignSub elmt
xml2Expression ("MultiplyAssignmentExpression",elmt)          = assignExpression OpAssignMul elmt
xml2Expression ("DivideAssignmentExpression",elmt)            = assignExpression OpAssignDiv elmt
xml2Expression ("ModuloAssignmentExpression",elmt)            = assignExpression OpAssignMod elmt
xml2Expression ("AndAssignmentExpression",elmt)               = assignExpression OpAssignBAnd elmt
xml2Expression ("ExclusiveOrAssignmentExpression",elmt)       = assignExpression OpAssignBXor elmt
xml2Expression ("OrAssignmentExpression",elmt)                = assignExpression OpAssignBOr elmt
xml2Expression ("LeftShiftAssignmentExpression",elmt)         = assignExpression OpAssignLShift elmt
xml2Expression ("SignedRightShiftAssignmentExpression",elmt)  = assignExpression OpAssignSpRShift elmt
xml2Expression ("UnsignedRightShiftAssignmentExpression",elmt)= assignExpression OpAssignZfRShift elmt
--Post-prefix Inc-decrement expressions
xml2Expression ("PreIncrementExpression",elmt)                = unaryAssignExpression PrefixInc elmt
xml2Expression ("PreDecrementExpression",elmt)                = unaryAssignExpression PrefixDec elmt
xml2Expression ("PostIncrementExpression",elmt)               = unaryAssignExpression PostfixInc elmt
xml2Expression ("PostDecrementExpression",elmt)               = unaryAssignExpression PostfixDec elmt
--Prefix expressions 
xml2Expression ("PlusExpression",elmt)                        = prefixExpression PrefixPlus elmt
xml2Expression ("NegateExpression",elmt)                      = prefixExpression PrefixMinus elmt
xml2Expression ("BitwiseNotExpression",elmt)                  = prefixExpression PrefixBNot elmt
xml2Expression ("LogicalNotExpression",elmt)                  = prefixExpression PrefixLNot elmt
xml2Expression ("TypeOfExpression",elmt)                      = prefixExpression PrefixTypeof elmt
xml2Expression ("VoidExpression",elmt)                        = prefixExpression PrefixVoid elmt
xml2Expression ("DeleteExpression",elmt)                      = prefixExpression PrefixDelete elmt
--ConditionalExpression has three children: conf, if-true, if-false
xml2Expression ("ConditionalExpression",elmt) = 
  let children = map xml2Expression (createPairs elmt) in
  CondExpr Nothing (head children) (head (tail children)) (last children)
--ParenthesizedExpression has one child: the content in parenthesis.
xml2Expression ("ParenthesizedExpression",elmt) = xml2Expression (getUniqueChild elmt)
--Identifier name: refernece to a variable (terminal)
xml2Expression ("IdentifierName",elmt) = VarRef Nothing (Id Nothing (getText elmt))
--Numeric literal is only one literal.
xml2Expression ("NumericLiteral",elmt) = numberLiteralExpression elmt
--String literal is only one literal.
xml2Expression ("StringLiteral",elmt) = StringLit Nothing (removeQuotes (getText elmt))
--Regularexpression:
xml2Expression ("RegularExpressionLiteral",elmt) = 
  let text = split (=='/')(getText elmt) in
  RegexpLit Nothing (head text) (isInfixOf "g" (last text)) (isInfixOf "i" (last text)) 
--Boolean Keywords:
xml2Expression ("TrueKeyword",_) = BoolLit Nothing True
xml2Expression ("FalseKeyword",_) = BoolLit Nothing False
--Null
xml2Expression ("NullKeyword",_) = NullLit Nothing 
--This
xml2Expression ("ThisKeyword",_) = ThisRef Nothing 
--EqualsValueClause contains only one child
xml2Expression ("EqualsValueClause",elmt) = xml2Expression (getUniqueChild elmt)
--Memebr acces expression has two children: the accesed object and the member.
xml2Expression ("MemberAccessExpression",el) = 
  let exprParts = (createPairs el) in
  let identifier = head exprParts in
  let member = last exprParts in
  DotRef Nothing (xml2Expression identifier) (Id Nothing (getText (snd member)))
--ElementAccessExpression contains 2 children: the subscriptable expr and the index expr.
xml2Expression ("ElementAccessExpression",el) =
  let exprParts = (map xml2Expression (createPairs el)) in
  BracketRef Nothing (head exprParts) (last exprParts)
--ArrayLiteralExpression contains a separated list of expressions
xml2Expression ("ArrayLiteralExpression",el) = 
  ArrayLit Nothing (xml2ListExpression (head (createPairs el)))
--CommaExpression contains a separated list of expressions
xml2Expression ("CommaExpression",el) = 
  ListExpr Nothing (map xml2Expression (createPairs el))
--InvocationExpression has an expression (the function) and a list (arguemnts)
xml2Expression ("InvocationExpression",elmt) = 
  let children = createPairs elmt in
  CallExpr Nothing (xml2Expression (head children)) (xml2ListExpression (last children))
--ObjectCreationExpression has an expression (the function) and a list (arguemnts)
xml2Expression ("ObjectCreationExpression",elmt) = 
  let children = createPairs elmt in
  NewExpr Nothing (xml2Expression (head children)) (xml2ListExpression (last children))
xml2Expression ("ObjectLiteralExpression",elmt) = 
  let children = createPairs elmt in
  ObjectLit Nothing (map propertyAssigmentExpression (createPairs(snd(head children))))
--Any other unsuported type
xml2Expression (s,_) = error ("Exception expression: string of type:" ++ s)

{-
  Given an element of the XML tree, return the corresponding Haskell 
  LValue object.
-}
xml2LValue :: (String,Element) -> LValue (Maybe (RType ()))
--Identifier name is a terminal: only contains the text with the Id
xml2LValue ("IdentifierName",elmt) = LVar Nothing (getText elmt)
--Member acces expression has two children: the accesed object and the member. 
--The member can only be an identifier so it's a string.
xml2LValue ("MemberAccessExpression",el) = 
  let exprParts = (createPairs el) in
  let identifier = head exprParts in
  let member = last exprParts in
  LDot Nothing (xml2Expression identifier) (getText (snd member)) 
--ElementAccessExpression contains 2 children: the subscriptable expr and the index expr.
xml2LValue ("ElementAccessExpression",el) =
  let exprParts = (map xml2Expression (createPairs el)) in
  LBracket Nothing (head exprParts) (last exprParts)
xml2LValue (s,_) = error ("Exception lvalue: string of type:" ++ s)

{-
  Given an element of the XML tree, return the corresponding Haskell 
  Id object.
-}
xml2Id :: (String,Element) -> Id (Maybe (RType ()))
xml2Id ("IdentifierName",el) = Id Nothing(getText el)
xml2Id ("Parameter",el) = xml2Id (head (createPairs el))
xml2Id (s,_) = error ("Exception id: string of type:" ++ s)

{-
  Given an infix operator and an element of kind "infix expression", extract the
  operands and construct an InfixExpr
-}
infixExpression :: InfixOp -> Element -> Expression (Maybe (RType ()))
infixExpression op el = 
  let operands = (map xml2Expression (createPairs el)) in
  InfixExpr Nothing op (head operands) (last operands)

{-
  Given an assignment operator and an element of kind "assign expression", extract the
  left and right side and construct an AssignExpr
-}
assignExpression :: AssignOp -> Element -> Expression (Maybe (RType ()))
assignExpression op el = 
  let sides = (createPairs el) in
  let left = head sides in
  let right = last sides in
  AssignExpr Nothing op (xml2LValue left) (xml2Expression right)

{-
  Given an unary assignment operator and an element of kind "unary assign expression",
  construct the corresponding UnaryAssignExpr
-}
unaryAssignExpression :: UnaryAssignOp -> Element -> Expression (Maybe (RType ()))
--there is only one child: the lvalue to be incremented or decremented
unaryAssignExpression op el =
  UnaryAssignExpr Nothing op (xml2LValue (head (createPairs el)))

{-
  Given an prefix operator and an element of kind "prefix expression",
  construct the corresponding PrefixExpr
-}
prefixExpression :: PrefixOp -> Element -> Expression (Maybe (RType ()))
--prefix expressions have only one child: the modified object
prefixExpression op el = 
  PrefixExpr Nothing op (xml2Expression (head (createPairs el)))

{-
  Read the literal number contained in the XML tag
  and convert it to a NumLit or IntLit
-}
numberLiteralExpression :: Element -> Expression (Maybe (RType ()))
--Choose between double and int
numberLiteralExpression el = 
  let text = (getText el) in
  if isInfixOf "." text then NumLit Nothing (read text :: Double)
  else IntLit Nothing (read text :: Int)

{-
  Convert a variabel declaration in XML element into a VarDecl.
  This is only for one variable. This function should eb called for 
  every declared variable ina statement of the form var a,b,c;
-}
variableDeclaratorExpression :: Element -> VarDecl (Maybe (RType ()))
variableDeclaratorExpression el =
    let varAndInit = (createPairs el) in
    if length varAndInit == 1 then -- no initialization
      VarDecl (getTypeAnnotation el) (Id Nothing (getText $ getUChildByTag el "IdentifierName")) Nothing
    else --initialization
      VarDecl (getTypeAnnotation el) (Id Nothing (getText $ getUChildByTag el "IdentifierName")) 
                      (Just (xml2Expression ("EqualsValueClause",getUChildByTag el "EqualsValueClause")))

{-
  Creates a CaseClause object from a CaseSwitchClause or DefaultSwitchClause
  in the XML tree.
-}
caseClauseExpression :: (String,Element) -> CaseClause (Maybe (RType ()))
caseClauseExpression ("CaseSwitchClause",el) = 
  let children = createPairs el in
  CaseClause Nothing (xml2Expression (children!!0)) (xml2ListStatement (children!!1))
caseClauseExpression ("DefaultSwitchClause",el) =
  let children = createPairs el in
  CaseDefault Nothing (xml2ListStatement (children!!0))
caseClauseExpression (s,_) = error ("Exception caseclause: string of type:" ++ s)


forInitExpression :: Element -> ForInit (Maybe (RType ()))
forInitExpression el = 
  let children = createPairs el in
  if length children == 0 then NoInit
  else 
    ExprInit (xml2Expression (head children))
    --This looks like a bug: should be this:
    --let subchild = head (createPairs (snd (head children))) in
    --if (qName (elName (snd subchild))) == "CommaExpression" then
      --VarInit (map variableDeclaratorExpression (map snd (createPairs (snd subchild))))
    --else ExprInit (xml2Expression subchild)

forCondExpression :: Element -> Maybe (Expression (Maybe (RType ())))
forCondExpression el = 
  let children = createPairs el in
  if length children == 0 then Nothing
    else Just (xml2Expression (head children))

forIncrExpression :: Element -> Maybe (Expression (Maybe (RType ())))
forIncrExpression el = 
  let children = createPairs el in
  if length children == 0 then Nothing
    else Just (xml2Expression (head children))

forInInitExpression :: Element -> ForInInit (Maybe (RType ()))
forInInitExpression el =
  if (qName (elName el)) == "VariableDeclaration" then
    ForInVar (Id Nothing (getText  (snd(head(createPairs(snd(head(createPairs(snd(head(createPairs el)))))))))))
  else 
    ForInLVal (xml2LValue ((qName (elName el)),el))

tryCatchFinnalyStatement :: Element -> Statement (Maybe (RType ()))
tryCatchFinnalyStatement el =
  let children = createPairs el in
  let extra = tail children in
  if length extra == 1 then --decide if its a catch or a finally
    if (fst (head extra)) == "CatchClause" then
      TryStmt Nothing (xml2Statement (head children)) (Just (catchClauseStatement (snd (head extra)))) Nothing
    else 
      TryStmt Nothing (xml2Statement (head children)) Nothing (Just(xml2Statement (head extra)))
  else --both are present
    TryStmt Nothing (xml2Statement (head children)) (Just (catchClauseStatement (snd (head extra)))) (Just(xml2Statement (last extra)))

catchClauseStatement :: Element -> CatchClause (Maybe (RType ()))
catchClauseStatement el = 
  let children = createPairs el in
  CatchClause Nothing (Id Nothing (getText (snd (head children)))) (xml2Statement (last children))  

propertyAssigmentExpression :: (String,Element) -> (Prop (Maybe (RType ())), Expression (Maybe (RType ())))
propertyAssigmentExpression (_,el) =
  let pair = createPairs el in
  let key = head pair in
  let value = last pair in
  if (qName (elName (snd key))) == "IdentifierName" then
    (PropId Nothing (Id Nothing (getText (snd key))), xml2Expression value)
  else if (qName (elName (snd key))) == "NumericLiteral" then
    (PropNum Nothing (read (getText (snd key)) :: Integer), xml2Expression value)
  else
    (PropString Nothing (removeQuotes(getText (snd key))), xml2Expression value)


getFunctionType :: Element -> (Maybe (RType ()))
getFunctionType el = 
  let signature = getUChildByTag el "CallSignature" in
  let parlist = getUChildByTag signature "ParameterList" in
  let params = snd $ getUniqueChild parlist in
  Just (TFun (functionParameterTypesList params) (functionReturnType signature) ())


functionParameterTypesList :: Element -> [Bind ()]
functionParameterTypesList separatedlist =
  let params = createPairs separatedlist in
  let fn acc (_,el) = acc++[formatParamsType el] in
  foldl fn [] params

formatParamsType :: Element -> Bind ()
formatParamsType el =
  let (x,t) = parameter2NameAndType el in 
  case t of
    Nothing ->     (B (F.stringSymbol x) (TApp TAny [] ()))
    Just ty ->     (B (F.stringSymbol x) ty)

parameter2NameAndType :: Element -> (String, Maybe(RType ()))
parameter2NameAndType el = ((getText (getUChildByTag el "IdentifierName")),
                          getTypeAnnotation el)

functionReturnType :: Element -> RType ()
functionReturnType el =
  let typeannotation = getTypeAnnotation el in
       case typeannotation  of 
                Nothing -> TApp TVoid [] ()
                Just ann  -> ann


getTypeAnnotation :: Element -> (Maybe (RType ()))
getTypeAnnotation el =
  let typeannotations = getChildByTag el "TypeAnnotation" in
  if length typeannotations > 1 then error ("Too many type type annotations")
  else if length typeannotations == 0 then Nothing
  else let typeannotation = typeannotations!!0 in
  let keyword_tag = getUniqueChild typeannotation in
  Just (convertTypeKeyword keyword_tag)

convertTypeKeyword :: (String,Element) -> RType ()
convertTypeKeyword ("NumberKeyword",_) = TApp TInt [] ()
convertTypeKeyword ("BooleanKeyword",_) = TApp TBool [] ()
convertTypeKeyword ("BoolKeyword",_) = TApp TBool [] ()
convertTypeKeyword ("StringKeyword",_) = TApp TString [] ()
convertTypeKeyword ("VoidKeyword",_) = TApp TVoid [] ()
convertTypeKeyword ("AnyKeyword",_) = TApp TAny [] ()
convertTypeKeyword ("ArrayType",el) = TArr (convertTypeKeyword $ getUniqueChild el) ()
convertTypeKeyword (str,_) = error ("Unsuported type "++str)
