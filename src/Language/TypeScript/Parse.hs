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

parseTypeScript :: FilePath -> IO (JavaScript (Maybe Type))
parseTypeScript fts
  = do fxml <- convertTs2XML fts
       parseTypeScriptXML fxml

-- | convertTs2XML takes a path to a .ts file and converts and returns a path to a .xml file
convertTs2XML :: FilePath -> IO FilePath
convertTs2XML inFile 
  = do executeShellCommand "ts2xml" convertCommand 
       return outFile
    where
       convertCommand = printf "%s %s > %s" convFile inFile outFile
       convFile       = "$HOME/CSE199/nano-ts/run" 
       outFile        = replaceExtension inFile ".xml"


parseTypeScriptXML :: FilePath -> IO (JavaScript (Maybe Type))
parseTypeScriptXML arg =
  do contents <- readFile arg
     case parseXMLDoc contents of -- returns a Maybe Element
        Nothing     -> error "Failed to parse xml"
        Just rootEl -> return $ xml2script rootEl

split     :: (Char -> Bool) -> String -> [String]
split p s = case dropWhile p s of
               "" -> []
               s' -> w : split p s''
                    where (w, s'') = break p s'

removequotes :: String -> String
removequotes s =
  if (head s) == '\"' || (head s) == '\'' then
    if (last s) == '\"' || (last s) == '\'' then (tail (init s))
    else (tail s)
  else if (last s) == '\"' || (last s) == '\'' then (init s)
    else s



--Takes an element and creates a list of pairs (s,e) where
  -- e is a child element of the passed element and s is the tagname of e.
createPairs :: Element -> [(String, Element)]
createPairs el  = [ (qName (elName e), e) | x@(Elem e) <- (elContent el)]


getChildByTag :: Element -> String -> [Element]
getChildByTag el str = 
  let target x = ((fst x) == str) in 
  map snd (filter target (createPairs el))

getUChildByTag :: Element -> String -> Element
getUChildByTag el str = 
  let pairs = getChildByTag el str in
  if length pairs > 1 then error ("The tag "++qName (elName el)++" should only have one child of tag"++str++".")
    else pairs!!0

getChildByRegex :: Element -> String -> [(String,Element)]
getChildByRegex el str = let target x = (((fst x) =~ str)::Bool) in filter target (createPairs el)

getUniqueChild :: Element -> (String,Element)
getUniqueChild el = let pairs = createPairs el in
  if length pairs > 1 then error ("The tag "++qName (elName el)++" should only have one child.")
  else head pairs

--Get the text contained in a tag (i.e. t in <tag>t</tag>)
getText :: Element -> String
getText el  = concat [ (cdData t) | x@(Text t) <- (elContent el)]

xml2script :: Element -> JavaScript (Maybe (RType ()))
--SourceUnit: has 1 child (List of statements).  --TODO correct, should not be a blockstmt
xml2script el = Script Nothing  (xml2list_statement (head (createPairs el)))

xml2statement :: (String,Element) -> Statement (Maybe (RType ()))
--SourceUnit: has 1 child (List of statements).  --TODO correct, should not be a blockstmt
--xml2statement ("SourceUnit",list) = BlockStmt Nothing (xml2list_statement (head (createPairs list)))
--Block has onle one child: a list.
xml2statement ("Block",elmt) = BlockStmt Nothing (xml2list_statement (head (getChildByRegex elmt "(.)*List$")))
--ExpressionStatement has one child: the expression.
xml2statement ("ExpressionStatement",elmt) = ExprStmt Nothing (xml2expression (getUniqueChild elmt))
--EmptyStatement has one child: the expression.
xml2statement ("EmptyStatement",elmt) = EmptyStmt Nothing
--IfStatement has 2 or 3 children: condition, if-true-statement, and optionally if-false-statement
xml2statement ("IfStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 2 then  --simple if
  IfSingleStmt Nothing (xml2expression (exprParts!!0)) 
                       (xml2statement (exprParts!!1)) 
  -- if with else
  else IfStmt Nothing (xml2expression (exprParts!!0)) 
                      (xml2statement (exprParts!!1)) 
                      (xml2statement ("ElseClause",getUChildByTag elmt "ElseClause")) 
--ElseClause can only have one clause (might be a block to contain more than one statement)
xml2statement ("ElseClause",elmt) = xml2statement (getUniqueChild elmt)
--ForStatement has four children.
xml2statement ("ForStatement",elmt) =
  ForStmt Nothing (forinit_expression (getUChildByTag elmt "ForLoopInit"))
                  (forcond_expression (getUChildByTag elmt "ForLoopTest"))
                  (forincr_expression (getUChildByTag elmt "ForLoopInc"))
                  (xml2statement $ (createPairs (getUChildByTag elmt "ForLoopBody"))!!0)             
--ForInStatement: three children: the iterator, the iterable and the block
xml2statement ("ForInStatement",elmt) =
  let pairs = createPairs elmt in
  ForInStmt Nothing (forininit_expression (snd (pairs!!0)))
                    (xml2expression (pairs!!1))
                    (xml2statement (pairs!!2))
--WhileStatement has 2 children: the condition and the body
xml2statement ("WhileStatement",elmt) = 
  let pairs = createPairs elmt in
  WhileStmt Nothing (xml2expression (pairs!!0)) (xml2statement (pairs!!1))
--DoStatement has 2 children (do-while)): the body and the condition
xml2statement ("DoStatement",elmt) = 
  let pairs = createPairs elmt in
  DoWhileStmt Nothing (xml2statement (pairs!!0)) (xml2expression (pairs!!1)) 
--ReturnStatement migh have a child or not.
xml2statement ("ReturnStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 0 then  ReturnStmt Nothing Nothing --empty return
  else ReturnStmt Nothing (Just (xml2expression (exprParts!!0)))
--Break/ContinueStatement might contain a label, or nothing.
--If there is a label, its in an IdentfierName tag under the breakstmt, so
--we extract the content from that tag
xml2statement ("BreakStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 0 then  BreakStmt Nothing Nothing --empty return
  else BreakStmt Nothing (Just (Id Nothing (getText (snd (exprParts!!0)))))
xml2statement ("ContinueStatement",elmt) = 
  let exprParts = createPairs elmt in
  if length exprParts == 0 then  ContinueStmt Nothing Nothing --empty return
  else ContinueStmt Nothing (Just (Id Nothing (getText (snd (exprParts!!0)))))
--LabeledStatement contains the label itself as  child in a IdentifierName tag
--and a Statement of any kind (only one!)
xml2statement ("LabeledStatement",elmt) =
  LabelledStmt Nothing (Id Nothing (getText (getUChildByTag elmt "IdentifierName"))) 
                       (xml2statement $ (createPairs elmt)!!1)
--VaribleStatement contisn a list of modifiers and the variabledeclaration statement wich contains a separatedlist
xml2statement ("VariableStatement",elmt) = 
  let sepList = snd $ (getChildByRegex (getUChildByTag elmt "VariableDeclaration") "(.)*List$")!!0 in
  VarDeclStmt Nothing (map variabledeclarator_expression (getChildByTag sepList "VariableDeclarator"))
--SwitchStatement contains the test expression and a list of Case/DefaultSwitchDlause
xml2statement ("SwitchStatement",elmt) =
  let children = createPairs elmt in 
  SwitchStmt Nothing  (xml2expression (children!!0)) 
                      (map caseclause_expression (getChildByRegex (snd $ (getChildByRegex elmt "(.)*List$")!!0) "(.)*SwitchClause"))
--WithStatement 2 children
xml2statement ("WithStatement",elmt) =
  let children = createPairs elmt in 
  WithStmt Nothing  (xml2expression (children!!0)) (xml2statement (children!!1))
--ThrowStatement contains only one child, expression.
xml2statement ("ThrowStatement",elmt) =
  let children = createPairs elmt in 
  ThrowStmt Nothing  (xml2expression (children!!0))
--FunctionDeclaration contains modifiers, name,args and body.
xml2statement ("FunctionDeclaration",elmt) =
  let children = createPairs elmt in
  FunctionStmt (get_function_type elmt) 
               (Id Nothing(getText $ getUChildByTag elmt "IdentifierName" )) 
               (xml2list_id ("ParameterList",(getUChildByTag (getUChildByTag elmt "CallSignature") "ParameterList"))) 
               [(xml2statement (children!!3))]
--TryStatement 
xml2statement ("TryStatement",elmt) = trycatchfinnaly_statement elmt
--FinallyClause contains only one child
xml2statement ("FinallyClause",elmt) = xml2statement $ (createPairs elmt)!!0
--Any other unsupported types
xml2statement (s,_) = error ("Exception statement: string of type:" ++ s)

xml2list_statement :: (String,Element) -> [Statement (Maybe (RType ()))]
--List is a generic list of statements.
xml2list_statement (_,elmt) = (map xml2statement (createPairs elmt))

xml2list_expression :: (String,Element) -> [Expression (Maybe (RType ()))]
--ARgumentList has only one child which is a list
xml2list_expression ("ArgumentList",elmt) = (xml2list_expression (getUniqueChild elmt))
--List is a generic list of expressions.
xml2list_expression (_,elmt) = (map xml2expression (createPairs elmt))

xml2list_id :: (String,Element) -> [Id (Maybe (RType ()))]
xml2list_id ("ParameterList",elmt) = xml2list_id (getUniqueChild elmt)
xml2list_id (s,elmt) = map xml2id (createPairs elmt)

xml2expression :: (String,Element) -> Expression (Maybe (RType ()))
--InfixExpressions:
-- They all have 2 children (left and right oprands).
xml2expression ("LogicalOrExpression",elmt) =                  infix_expression OpLOr elmt
xml2expression ("LogicalAndExpression",elmt) =                 infix_expression OpLAnd elmt 
xml2expression ("BitwiseOrExpression",elmt) =                  infix_expression OpBOr elmt 
xml2expression ("BitwiseExclusiveOrExpression",elmt) =         infix_expression OpBXor elmt 
xml2expression ("BitwiseAndExpression",elmt) =                 infix_expression OpBAnd elmt 
xml2expression ("EqualsWithTypeConversionExpression",elmt) =   infix_expression OpEq elmt 
xml2expression ("NotEqualsWithTypeConversionExpression",elmt) =infix_expression OpNEq elmt 
xml2expression ("EqualsExpression",elmt) =                     infix_expression OpStrictEq elmt 
xml2expression ("NotEqualsExpression",elmt) =                  infix_expression OpStrictNEq elmt  
xml2expression ("LessThanExpression",elmt) =                   infix_expression OpLT elmt 
xml2expression ("GreaterThanExpression",elmt) =                infix_expression OpGT elmt 
xml2expression ("LessThanOrEqualExpression",elmt) =            infix_expression OpLEq elmt 
xml2expression ("GreaterThanOrEqualExpression",elmt) =         infix_expression OpGEq elmt 
xml2expression ("InstanceOfExpression",elmt) =                 infix_expression OpInstanceof elmt 
xml2expression ("InExpression",elmt) =                         infix_expression OpIn elmt 
xml2expression ("LeftShiftExpression",elmt) =                  infix_expression OpLShift elmt 
xml2expression ("SignedRightShiftExpression",elmt) =           infix_expression OpSpRShift elmt 
xml2expression ("UnsignedRightShiftExpression",elmt) =         infix_expression OpZfRShift elmt 
xml2expression ("MultiplyExpression",elmt) =                   infix_expression OpMul elmt 
xml2expression ("DivideExpression",elmt) =                     infix_expression OpDiv elmt 
xml2expression ("ModuloExpression",elmt) =                     infix_expression OpMod elmt 
xml2expression ("AddExpression",elmt) =                        infix_expression OpAdd elmt 
xml2expression ("SubtractExpression",elmt) =                   infix_expression OpSub elmt 
--AssignExpr: two children: the LValue and the right expression.
xml2expression ("AssignmentExpression",elmt) =                 assign_expression OpAssign elmt
xml2expression ("AddAssignmentExpression",elmt) =              assign_expression OpAssignAdd elmt
xml2expression ("SubtractAssignmentExpression",elmt) =         assign_expression OpAssignSub elmt
xml2expression ("MultiplyAssignmentExpression",elmt) =         assign_expression OpAssignMul elmt
xml2expression ("DivideAssignmentExpression",elmt) =           assign_expression OpAssignDiv elmt
xml2expression ("ModuloAssignmentExpression",elmt) =           assign_expression OpAssignMod elmt
xml2expression ("AndAssignmentExpression",elmt) =              assign_expression OpAssignBAnd elmt
xml2expression ("ExclusiveOrAssignmentExpression",elmt) =      assign_expression OpAssignBXor elmt
xml2expression ("OrAssignmentExpression",elmt) =               assign_expression OpAssignBOr elmt
xml2expression ("LeftShiftAssignmentExpression",elmt) =        assign_expression OpAssignLShift elmt
xml2expression ("SignedRightShiftAssignmentExpression",elmt) = assign_expression OpAssignSpRShift elmt
xml2expression ("UnsignedRightShiftAssignmentExpression",elmt)=assign_expression OpAssignZfRShift elmt
--Post-prefix Inc-decrement expressions
xml2expression ("PreIncrementExpression",elmt) =               unaryassign_expression PrefixInc elmt
xml2expression ("PreDecrementExpression",elmt) =               unaryassign_expression PrefixDec elmt
xml2expression ("PostIncrementExpression",elmt) =              unaryassign_expression PostfixInc elmt
xml2expression ("PostDecrementExpression",elmt) =              unaryassign_expression PostfixDec elmt
--Prefix expressions 
xml2expression ("PlusExpression",elmt) =                       prefix_expression PrefixPlus elmt
xml2expression ("NegateExpression",elmt) =                     prefix_expression PrefixMinus elmt
xml2expression ("BitwiseNotExpression",elmt) =                 prefix_expression PrefixBNot elmt
xml2expression ("LogicalNotExpression",elmt) =                 prefix_expression PrefixLNot elmt
xml2expression ("TypeOfExpression",elmt) =                     prefix_expression PrefixTypeof elmt
xml2expression ("VoidExpression",elmt) =                       prefix_expression PrefixVoid elmt
xml2expression ("DeleteExpression",elmt) =                     prefix_expression PrefixDelete elmt
--ConditionalExpression has three children: conf, if-true, if-false
xml2expression ("ConditionalExpression",elmt) = 
  let children = map xml2expression (createPairs elmt) in
  CondExpr Nothing (head children) (head (tail children)) (last children)
--ParenthesizedExpression has one child: the content in parenthesis.
xml2expression ("ParenthesizedExpression",elmt) = xml2expression (getUniqueChild elmt)
--Identifier name: refernece to a variable (terminal)
xml2expression ("IdentifierName",elmt) = VarRef Nothing (Id Nothing (getText elmt))
--Numeric literal is only one literal.
xml2expression ("NumericLiteral",elmt) = numberliteral_expression elmt
--String literal is only one literal.
xml2expression ("StringLiteral",elmt) = StringLit Nothing (removequotes (getText elmt))
--Regularexpression:
xml2expression ("RegularExpressionLiteral",elmt) = 
  let text = split (=='/')(getText elmt) in
  RegexpLit Nothing (head text) (isInfixOf "g" (last text)) (isInfixOf "i" (last text)) 
--Boolean Keywords:
xml2expression ("TrueKeyword",_) = BoolLit Nothing True
xml2expression ("FalseKeyword",_) = BoolLit Nothing False
--Null
xml2expression ("NullKeyword",_) = NullLit Nothing 
--This
xml2expression ("ThisKeyword",_) = ThisRef Nothing 
--EqualsValueClause contains only one child
xml2expression ("EqualsValueClause",elmt) = xml2expression (getUniqueChild elmt)
--Memebr acces expression has two children: the accesed object and the member.
xml2expression ("MemberAccessExpression",el) = 
  let exprParts = (createPairs el) in
  let identifier = head exprParts in
  let member = last exprParts in
  DotRef Nothing (xml2expression identifier) (Id Nothing (getText (snd member)))
--ElementAccessExpression contains 2 children: the subscriptable expr and the index expr.
xml2expression ("ElementAccessExpression",el) =
  let exprParts = (map xml2expression (createPairs el)) in
  BracketRef Nothing (head exprParts) (last exprParts)
--ArrayLiteralExpression contains a separated list of expressions
xml2expression ("ArrayLiteralExpression",el) = 
  ArrayLit Nothing (xml2list_expression (head (createPairs el)))
--CommaExpression contains a separated list of expressions
xml2expression ("CommaExpression",el) = 
  ListExpr Nothing (map xml2expression (createPairs el))
--InvocationExpression has an expression (the function) and a list (arguemnts)
xml2expression ("InvocationExpression",elmt) = 
  let children = createPairs elmt in
  CallExpr Nothing (xml2expression (head children)) (xml2list_expression (last children))
--ObjectCreationExpression has an expression (the function) and a list (arguemnts)
xml2expression ("ObjectCreationExpression",elmt) = 
  let children = createPairs elmt in
  NewExpr Nothing (xml2expression (head children)) (xml2list_expression (last children))
xml2expression ("ObjectLiteralExpression",elmt) = 
  let children = createPairs elmt in
  ObjectLit Nothing (map propertyassigment_expression (createPairs(snd(head children))))
--Any other unsuported type
xml2expression (s,_) = error ("Exception expression: string of type:" ++ s)


xml2lvalue :: (String,Element) -> LValue (Maybe (RType ()))
--Identifier name is a terminal: only contains the text with the Id
xml2lvalue ("IdentifierName",elmt) = LVar Nothing (getText elmt)
--Member acces expression has two children: the accesed object and the member. 
--The member can only be an identifier so it's a string.
xml2lvalue ("MemberAccessExpression",el) = 
  let exprParts = (createPairs el) in
  let identifier = head exprParts in
  let member = last exprParts in
  LDot Nothing (xml2expression identifier) (getText (snd member)) 
--ElementAccessExpression contains 2 children: the subscriptable expr and the index expr.
xml2lvalue ("ElementAccessExpression",el) =
  let exprParts = (map xml2expression (createPairs el)) in
  LBracket Nothing (head exprParts) (last exprParts)
xml2lvalue (s,_) = error ("Exception lvalue: string of type:" ++ s)

xml2id :: (String,Element) -> Id (Maybe (RType ()))
xml2id ("IdentifierName",el) = Id Nothing(getText el)
xml2id ("Parameter",el) = xml2id (head (createPairs el))
xml2id (s,_) = error ("Exception id: string of type:" ++ s)

infix_expression :: InfixOp -> Element -> Expression (Maybe (RType ()))
infix_expression op el = 
  let operands = (map xml2expression (createPairs el)) in
  InfixExpr Nothing op (head operands) (last operands)

assign_expression :: AssignOp -> Element -> Expression (Maybe (RType ()))
assign_expression op el = 
  let sides = (createPairs el) in
  let left = head sides in
  let right = last sides in
  AssignExpr Nothing op (xml2lvalue left) (xml2expression right)

unaryassign_expression :: UnaryAssignOp -> Element -> Expression (Maybe (RType ()))
--there is only one child: the lvalue to be incremented or decremented
unaryassign_expression op el =
  UnaryAssignExpr Nothing op (xml2lvalue (head (createPairs el)))

prefix_expression :: PrefixOp -> Element -> Expression (Maybe (RType ()))
--prefix expressions have only one child: the modified object
prefix_expression op el = 
  PrefixExpr Nothing op (xml2expression (head (createPairs el)))


numberliteral_expression :: Element -> Expression (Maybe (RType ()))
--Choose between double and int
numberliteral_expression el = 
  let text = (getText el) in
  if isInfixOf "." text then NumLit Nothing (read text :: Double)
  else IntLit Nothing (read text :: Int)


variabledeclarator_expression :: Element -> VarDecl (Maybe (RType ()))
variabledeclarator_expression el =
    let varAndInit = (createPairs el) in
    if length varAndInit == 1 then -- no initialization
      VarDecl (get_type_annotation el) (Id Nothing (getText $ getUChildByTag el "IdentifierName")) Nothing
    else --initialization
      VarDecl (get_type_annotation el) (Id Nothing (getText $ getUChildByTag el "IdentifierName")) 
                      (Just (xml2expression ("EqualsValueClause",getUChildByTag el "EqualsValueClause")))

caseclause_expression :: (String,Element) -> CaseClause (Maybe (RType ()))
caseclause_expression ("CaseSwitchClause",el) = 
  let children = createPairs el in
  CaseClause Nothing (xml2expression (children!!0)) (xml2list_statement (children!!1))
caseclause_expression ("DefaultSwitchClause",el) =
  let children = createPairs el in
  CaseDefault Nothing (xml2list_statement (children!!0))
caseclause_expression (s,_) = error ("Exception caseclause: string of type:" ++ s)

forinit_expression :: Element -> ForInit (Maybe (RType ()))
forinit_expression el = 
  let children = createPairs el in
  if length children == 0 then NoInit
  else 
    ExprInit (xml2expression (head children))
    --This looks like a bug: should be this:
    --let subchild = head (createPairs (snd (head children))) in
    --if (qName (elName (snd subchild))) == "CommaExpression" then
      --VarInit (map variabledeclarator_expression (map snd (createPairs (snd subchild))))
    --else ExprInit (xml2expression subchild)

forcond_expression :: Element -> Maybe (Expression (Maybe (RType ())))
forcond_expression el = 
  let children = createPairs el in
  if length children == 0 then Nothing
    else Just (xml2expression (head children))

forincr_expression :: Element -> Maybe (Expression (Maybe (RType ())))
forincr_expression el = 
  let children = createPairs el in
  if length children == 0 then Nothing
    else Just (xml2expression (head children))

forininit_expression :: Element -> ForInInit (Maybe (RType ()))
forininit_expression el =
  if (qName (elName el)) == "VariableDeclaration" then
    ForInVar (Id Nothing (getText  (snd(head(createPairs(snd(head(createPairs(snd(head(createPairs el)))))))))))
  else 
    ForInLVal (xml2lvalue ((qName (elName el)),el))

trycatchfinnaly_statement :: Element -> Statement (Maybe (RType ()))
trycatchfinnaly_statement el =
  let children = createPairs el in
  let extra = tail children in
  if length extra == 1 then --decide if its a catch or a finally
    if (fst (head extra)) == "CatchClause" then
      TryStmt Nothing (xml2statement (head children)) (Just (catchclause_statement (snd (head extra)))) Nothing
    else 
      TryStmt Nothing (xml2statement (head children)) Nothing (Just(xml2statement (head extra)))
  else --both are present
    TryStmt Nothing (xml2statement (head children)) (Just (catchclause_statement (snd (head extra)))) (Just(xml2statement (last extra)))

catchclause_statement :: Element -> CatchClause (Maybe (RType ()))
catchclause_statement el = 
  let children = createPairs el in
  CatchClause Nothing (Id Nothing (getText (snd (head children)))) (xml2statement (last children))  

propertyassigment_expression :: (String,Element) -> (Prop (Maybe (RType ())), Expression (Maybe (RType ())))
propertyassigment_expression (_,el) =
  let pair = createPairs el in
  let key = head pair in
  let value = last pair in
  if (qName (elName (snd key))) == "IdentifierName" then
    (PropId Nothing (Id Nothing (getText (snd key))), xml2expression value)
  else if (qName (elName (snd key))) == "NumericLiteral" then
    (PropNum Nothing (read (getText (snd key)) :: Integer), xml2expression value)
  else
    (PropString Nothing (removequotes(getText (snd key))), xml2expression value)


get_function_type :: Element -> (Maybe (RType ()))
get_function_type el = 
  let signature = getUChildByTag el "CallSignature" in
  let parlist = getUChildByTag signature "ParameterList" in
  let params = snd $ getUniqueChild parlist in
  Just (TFun (function_parameter_types_list params) (function_return_type signature) ())


function_parameter_types_list :: Element -> [Bind ()]
function_parameter_types_list separatedlist =
  let params = createPairs separatedlist in
  let fn acc (_,el) = acc++[format_par_type el] in
  foldl fn [] params

format_par_type :: Element -> Bind ()
format_par_type el =
  let (x,t) = parameter_name_type el in 
  case t of
    Nothing ->     (B (F.stringSymbol x) (TApp TAny [] ()))
    Just ty ->     (B (F.stringSymbol x) ty)

parameter_name_type :: Element -> (String, Maybe(RType ()))
parameter_name_type el = ((getText (getUChildByTag el "IdentifierName")),
                          get_type_annotation el)

function_return_type :: Element -> RType ()
function_return_type el =
  let typeannotation = get_type_annotation el in
       case typeannotation  of 
                Nothing -> TApp TVoid [] ()
                Just ann  -> ann


get_type_annotation :: Element -> (Maybe (RType ()))
get_type_annotation el =
  let typeannotations = getChildByTag el "TypeAnnotation" in
  if length typeannotations > 1 then error ("Too many type type annotations")
  else if length typeannotations == 0 then Nothing
  else let typeannotation = typeannotations!!0 in
  let keyword_tag = getUniqueChild typeannotation in
  Just (convert_type_keyword keyword_tag)

convert_type_keyword :: (String,Element) -> RType ()
convert_type_keyword ("NumberKeyword",_) = TApp TInt [] ()
convert_type_keyword ("BooleanKeyword",_) = TApp TBool [] ()
convert_type_keyword ("BoolKeyword",_) = TApp TBool [] ()
convert_type_keyword ("StringKeyword",_) = TApp TString [] ()
convert_type_keyword ("VoidKeyword",_) = TApp TVoid [] ()
convert_type_keyword ("AnyKeyword",_) = TApp TAny [] ()
convert_type_keyword ("ArrayType",el) = TArr (convert_type_keyword $ getUniqueChild el) ()
convert_type_keyword (str,_) = error ("Unsuported type "++str)
