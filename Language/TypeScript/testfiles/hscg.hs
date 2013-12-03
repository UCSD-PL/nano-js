import Language.ECMAScript3.Parser
import System.Environment
import System.IO

main = do (arg :_) <- getArgs
          contents <- readFile arg
          print (parseScriptFromString arg contents)



