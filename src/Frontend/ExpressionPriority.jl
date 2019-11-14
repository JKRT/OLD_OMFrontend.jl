module ExpressionPriority

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
#= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

import DAE
import Util

#= Determines whether an operand in an expression needs parentheses around it. =#
function shouldParenthesize(inOperand::DAE.Exp, inOperator::DAE.Exp, inLhs::Bool) ::Bool
     local outShouldParenthesize::Bool

     outShouldParenthesize = begin
         local diff::ModelicaInteger
       @match (inOperand, inOperator, inLhs) begin
         (DAE.UNARY(__), _, _)  => begin
           true
         end

         _  => begin
               diff = Util.intCompare(priority(inOperand, inLhs), priority(inOperator, inLhs))
             shouldParenthesize2(diff, inOperand, inLhs)
         end
       end
     end
 outShouldParenthesize
end

function shouldParenthesize2(inPrioDiff::ModelicaInteger, inOperand::DAE.Exp, inLhs::Bool) ::Bool
     local outShouldParenthesize::Bool

     outShouldParenthesize = begin
       @match (inPrioDiff, inOperand, inLhs) begin
         (1, _, _)  => begin
           true
         end

         (0, _, false)  => begin
           ! isAssociativeExp(inOperand)
         end

         _  => begin
             false
         end
       end
     end
 outShouldParenthesize
end

#= Determines whether the given expression represents an associative operation or not. =#
function isAssociativeExp(inExp::DAE.Exp) ::Bool
     local outIsAssociative::Bool

     outIsAssociative = begin
         local op::DAE.Operator
       @match inExp begin
         DAE.BINARY(operator = op)  => begin
           isAssociativeOp(op)
         end

         DAE.LBINARY(__)  => begin
           true
         end

         _  => begin
             false
         end
       end
     end
 outIsAssociative
end

#= Determines whether the given operator is associative or not. =#
function isAssociativeOp(inOperator::DAE.Operator) ::Bool
     local outIsAssociative::Bool

     outIsAssociative = begin
       @match inOperator begin
         DAE.ADD(__)  => begin
           true
         end

         DAE.MUL(__)  => begin
           true
         end

         DAE.ADD_ARR(__)  => begin
           true
         end

         DAE.MUL_ARRAY_SCALAR(__)  => begin
           true
         end

         DAE.ADD_ARRAY_SCALAR(__)  => begin
           true
         end

         _  => begin
             false
         end
       end
     end
 outIsAssociative
end

#= Returns an integer priority given an expression, which is used by
  ExpressionDumpTpl to add parentheses when dumping expressions. The inLhs
  argument should be true if the expression occurs on the left side of a binary
  operation, otherwise false. This is because we don't need to add parentheses
  to expressions such as x * y / z, but x / (y * z) needs them, so the
  priorities of some binary operations differ depending on which side they are. =#
function priority(inExp::DAE.Exp, inLhs::Bool) ::ModelicaInteger
     local outPriority::ModelicaInteger

     outPriority = begin
         local op::DAE.Operator
       @match (inExp, inLhs) begin
         (DAE.BINARY(operator = op), false)  => begin
           priorityBinopRhs(op)
         end

         (DAE.BINARY(operator = op), true)  => begin
           priorityBinopLhs(op)
         end

         (DAE.RCONST(__), _) where (inExp.real < 0.0)  => begin
           4
         end

         (DAE.UNARY(__), _)  => begin
           4
         end

         (DAE.LBINARY(operator = op), _)  => begin
           priorityLBinop(op)
         end

         (DAE.LUNARY(__), _)  => begin
           7
         end

         (DAE.RELATION(__), _)  => begin
           6
         end

         (DAE.RANGE(__), _)  => begin
           10
         end

         (DAE.IFEXP(__), _)  => begin
           11
         end

         _  => begin
             0
         end
       end
     end
      #=  Same as unary minus of a real literal
      =#
 outPriority
end

#= Returns the priority for a binary operation on the left hand side. Add and
  sub has the same priority, and mul and div too, in contrast with
  priorityBinopRhs. =#
function priorityBinopLhs(inOp::DAE.Operator) ::ModelicaInteger
     local outPriority::ModelicaInteger

     outPriority = begin
       @match inOp begin
         DAE.ADD(__)  => begin
           5
         end

         DAE.SUB(__)  => begin
           5
         end

         DAE.MUL(__)  => begin
           2
         end

         DAE.DIV(__)  => begin
           2
         end

         DAE.POW(__)  => begin
           1
         end

         DAE.ADD_ARR(__)  => begin
           5
         end

         DAE.SUB_ARR(__)  => begin
           5
         end

         DAE.MUL_ARR(__)  => begin
           2
         end

         DAE.DIV_ARR(__)  => begin
           2
         end

         DAE.MUL_ARRAY_SCALAR(__)  => begin
           2
         end

         DAE.ADD_ARRAY_SCALAR(__)  => begin
           5
         end

         DAE.SUB_SCALAR_ARRAY(__)  => begin
           5
         end

         DAE.MUL_SCALAR_PRODUCT(__)  => begin
           2
         end

         DAE.MUL_MATRIX_PRODUCT(__)  => begin
           2
         end

         DAE.DIV_ARRAY_SCALAR(__)  => begin
           2
         end

         DAE.DIV_SCALAR_ARRAY(__)  => begin
           2
         end

         DAE.POW_ARRAY_SCALAR(__)  => begin
           1
         end

         DAE.POW_SCALAR_ARRAY(__)  => begin
           1
         end

         DAE.POW_ARR(__)  => begin
           1
         end

         DAE.POW_ARR2(__)  => begin
           1
         end
       end
     end
 outPriority
end

#= Returns the priority for a binary operation on the right hand side. Add and
  sub has different priorities, and mul and div too, in contrast with
  priorityBinopLhs. =#
function priorityBinopRhs(inOp::DAE.Operator) ::ModelicaInteger
     local outPriority::ModelicaInteger

     outPriority = begin
       @match inOp begin
         DAE.ADD(__)  => begin
           6
         end

         DAE.SUB(__)  => begin
           5
         end

         DAE.MUL(__)  => begin
           3
         end

         DAE.DIV(__)  => begin
           2
         end

         DAE.POW(__)  => begin
           1
         end

         DAE.ADD_ARR(__)  => begin
           6
         end

         DAE.SUB_ARR(__)  => begin
           5
         end

         DAE.MUL_ARR(__)  => begin
           3
         end

         DAE.DIV_ARR(__)  => begin
           2
         end

         DAE.MUL_ARRAY_SCALAR(__)  => begin
           3
         end

         DAE.ADD_ARRAY_SCALAR(__)  => begin
           6
         end

         DAE.SUB_SCALAR_ARRAY(__)  => begin
           5
         end

         DAE.MUL_SCALAR_PRODUCT(__)  => begin
           3
         end

         DAE.MUL_MATRIX_PRODUCT(__)  => begin
           3
         end

         DAE.DIV_ARRAY_SCALAR(__)  => begin
           2
         end

         DAE.DIV_SCALAR_ARRAY(__)  => begin
           2
         end

         DAE.POW_ARRAY_SCALAR(__)  => begin
           1
         end

         DAE.POW_SCALAR_ARRAY(__)  => begin
           1
         end

         DAE.POW_ARR(__)  => begin
           1
         end

         DAE.POW_ARR2(__)  => begin
           1
         end
       end
     end
 outPriority
end

function priorityLBinop(inOp::DAE.Operator) ::ModelicaInteger
     local outPriority::ModelicaInteger

     outPriority = begin
       @match inOp begin
         DAE.AND(__)  => begin
           8
         end

         DAE.OR(__)  => begin
           9
         end
       end
     end
 outPriority
end


end
