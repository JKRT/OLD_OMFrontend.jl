module InstInterface

using MetaModelica
using ExportAll

import Patternm

function elabPatternCheckDuplicateBindings(cache::FCore.Cache, env::FCore.Graph, lhs::Absyn.Exp, ty::DAE.Type, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Pattern}
  Patternm.elabPatternCheckDuplicateBindings(cache, env, lhs, ty, info)
end

function traversePattern(inPattern::DAE.Pattern, func::Func, inExtra::TypeA)  where {TypeA}
  Patternm.traversePattern(inPattern, func, inExtra)
end
  
@exportAll

end
