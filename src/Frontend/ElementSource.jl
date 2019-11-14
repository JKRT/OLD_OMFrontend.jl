  module ElementSource


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

        import DAE
        import Prefix

        import Absyn
        import Error
        import CrefForHashTable
        import ListUtil
        import SCode
        import Flags

        function myMergeSources(src1::DAE.ElementSource, src2::DAE.ElementSource) ::DAE.ElementSource
              local myMergedSrc::DAE.ElementSource

              myMergedSrc = begin
                  local info::SourceInfo
                  local partOfLst1::List{Absyn.Within}
                  local partOfLst2::List{Absyn.Within}
                  local p::List{Absyn.Within}
                  local instanceOpt1::Prefix.ComponentPrefix
                  local instanceOpt2::Prefix.ComponentPrefix
                  local i::Prefix.ComponentPrefix
                  local connectEquationOptLst1::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                  local connectEquationOptLst2::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                  local c::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                  local typeLst1::List{Absyn.Path}
                  local typeLst2::List{Absyn.Path}
                  local t::List{Absyn.Path}
                  local o::List{DAE.SymbolicOperation}
                  local operations1::List{DAE.SymbolicOperation}
                  local operations2::List{DAE.SymbolicOperation}
                  local comment::List{SCode.Comment}
                  local comment1::List{SCode.Comment}
                  local comment2::List{SCode.Comment}
                @match (src1, src2) begin
                  (DAE.SOURCE(info, partOfLst1, instanceOpt1, connectEquationOptLst1, typeLst1, operations1, comment1), DAE.SOURCE(_, partOfLst2, instanceOpt2, connectEquationOptLst2, typeLst2, operations2, comment2))  => begin
                      p = ListUtil.union(partOfLst1, partOfLst2)
                      i = begin
                        @match instanceOpt1 begin
                          Prefix.NOCOMPPRE(__)  => begin
                            instanceOpt2
                          end

                          _  => begin
                              instanceOpt1
                          end
                        end
                      end
                      c = ListUtil.union(connectEquationOptLst1, connectEquationOptLst2)
                      t = ListUtil.union(typeLst1, typeLst2)
                      o = listAppend(operations1, operations2)
                      comment = ListUtil.union(comment1, comment2)
                    DAE.SOURCE(info, p, i, c, t, o, comment)
                  end
                end
              end
               #= /* Discard */ =#
          myMergedSrc
        end

        function addCommentToSource(source::DAE.ElementSource, commentIn::Option{<:SCode.Comment}) ::DAE.ElementSource


              source = begin
                  local info::SourceInfo
                  local partOfLst1::List{Absyn.Within}
                  local instanceOpt1::Prefix.ComponentPrefix
                  local connectEquationOptLst1::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                  local typeLst1::List{Absyn.Path}
                  local operations1::List{DAE.SymbolicOperation}
                  local comment1::List{SCode.Comment}
                  local comment2::List{SCode.Comment}
                  local comment::SCode.Comment
                @match (source, commentIn) begin
                  (DAE.SOURCE(_, _, _, _, _, _, _), SOME(comment))  => begin
                      source.comment = _cons(comment, source.comment)
                    source
                  end

                  _  => begin
                      source
                  end
                end
              end
          source
        end

         #= @author: adrpo
         set the various sources of the element =#
        function createElementSource(fileInfo::SourceInfo, partOf::Option{<:Absyn.Path} = NONE() #= the model(s) this element came from =#, prefix::Prefix.PrefixType = Prefix.NOPRE() #= the instance(s) this element is part of =#, connectEquation::Tuple{<:DAE.ComponentRef, DAE.ComponentRef} = (DAE.emptyCref, DAE.emptyCref) #= this element came from this connect(s) =#) ::DAE.ElementSource
              local source::DAE.ElementSource

              local path::Absyn.Path

              source = DAE.SOURCE(fileInfo, begin
                @match partOf begin
                  NONE()  => begin
                    nil
                  end

                  SOME(path)  => begin
                    list(Absyn.WITHIN(path))
                  end
                end
              end, begin
                @match prefix begin
                  Prefix.NOPRE(__)  => begin
                    Prefix.NOCOMPPRE()
                  end

                  Prefix.PREFIX(__)  => begin
                    prefix.compPre
                  end
                end
              end, begin
                @match connectEquation begin
                  (DAE.CREF_IDENT(ident = ""), _)  => begin
                    nil
                  end

                  _  => begin
                      list(connectEquation)
                  end
                end
              end, nil, nil, nil)
          source
        end

        function addAdditionalComment(source::DAE.ElementSource, message::String) ::DAE.ElementSource
              local outSource::DAE.ElementSource

              outSource = begin
                  local info::SourceInfo #= the line and column numbers of the equations and algorithms this element came from =#
                  local typeLst::List{Absyn.Path} #= the absyn type of the element =#
                  local partOfLst::List{Absyn.Within} #= the models this element came from =#
                  local instanceOpt::Prefix.ComponentPrefix #= the instance this element is part of =#
                  local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}} #= this element came from this connect =#
                  local operations::List{DAE.SymbolicOperation}
                  local comment::List{SCode.Comment}
                  local b::Bool
                  local c::SCode.Comment
                @match (source, message) begin
                  (DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, comment), _)  => begin
                      c = SCode.COMMENT(NONE(), SOME(message))
                      b = listMember(c, comment)
                      comment = if b
                            comment
                          else
                            _cons(c, comment)
                          end
                    DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, comment)
                  end
                end
              end
          outSource
        end

        function addAnnotation(source::DAE.ElementSource, comment::SCode.Comment) ::DAE.ElementSource
              local outSource::DAE.ElementSource

              outSource = begin
                  local info::SourceInfo #= the line and column numbers of the equations and algorithms this element came from =#
                  local typeLst::List{Absyn.Path} #= the absyn type of the element =#
                  local partOfLst::List{Absyn.Within} #= the models this element came from =#
                  local instanceOpt::Prefix.ComponentPrefix #= the instance this element is part of =#
                  local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}} #= this element came from this connect =#
                  local operations::List{DAE.SymbolicOperation}
                  local commentLst::List{SCode.Comment}
                  local b::Bool
                  local c::SCode.Comment
                @match (source, comment) begin
                  (DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, commentLst), SCode.COMMENT(annotation_ = SOME(_)))  => begin
                    DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, _cons(comment, commentLst))
                  end

                  _  => begin
                      source
                  end
                end
              end
          outSource
        end

        function getCommentsFromSource(source::DAE.ElementSource) ::List{SCode.Comment}
              local outComments::List{SCode.Comment}

              outComments = begin
                  local comment::List{SCode.Comment}
                @match source begin
                  DAE.SOURCE(comment = comment)  => begin
                    comment
                  end
                end
              end
          outComments
        end

        function addSymbolicTransformation(source::DAE.ElementSource, op::DAE.SymbolicOperation) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = begin
                  local info::SourceInfo #= the line and column numbers of the equations and algorithms this element came from =#
                  local typeLst::List{Absyn.Path} #= the absyn type of the element =#
                  local partOfLst::List{Absyn.Within} #= the models this element came from =#
                  local instanceOpt::Prefix.ComponentPrefix #= the instance this element is part of =#
                  local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}} #= this element came from this connect =#
                  local operations::List{DAE.SymbolicOperation}
                  local h1::DAE.Exp
                  local t1::DAE.Exp
                  local t2::DAE.Exp
                  local es1::List{DAE.Exp}
                  local es2::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local comment::List{SCode.Comment}
                @match (source, op) begin
                  (DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, DAE.SUBSTITUTION(es1 && h1 <| _, t1) <| operations, comment), DAE.SUBSTITUTION(es2, t2)) where (CrefForHashTable.expEqual(t2, h1))  => begin
                      es = listAppend(es2, es1)
                    DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, _cons(DAE.SUBSTITUTION(es, t1), operations), comment)
                  end

                  (DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, comment), _)  => begin
                    DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, _cons(op, operations), comment)
                  end
                end
              end
               #=  The tail of the new substitution chain is the same as the head of the old one...
               =#
               #=  Reference equality would be fine as otherwise it is not really a chain... But replaceExp is stupid :(
               =#
               #=  true = referenceEq(t2,h1);
               =#
          source
        end

        function condAddSymbolicTransformation(cond::Bool, source::DAE.ElementSource, op::DAE.SymbolicOperation) ::DAE.ElementSource


              if ! cond
                return source
              end
              source = addSymbolicTransformation(source, op)
          source
        end

        function addSymbolicTransformationDeriveLst(source::DAE.ElementSource, explst1::List{<:DAE.Exp}, explst2::List{<:DAE.Exp}) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = begin
                  local op::DAE.SymbolicOperation
                  local rexplst1::List{DAE.Exp}
                  local rexplst2::List{DAE.Exp}
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                @match (explst1, explst2) begin
                  ( nil(), _)  => begin
                    source
                  end

                  (exp1 <| rexplst1, exp2 <| rexplst2)  => begin
                      op = DAE.OP_DIFFERENTIATE(DAE.crefTime, exp1, exp2)
                      source = addSymbolicTransformation(source, op)
                    addSymbolicTransformationDeriveLst(source, rexplst1, rexplst2)
                  end
                end
              end
          source
        end

        function addSymbolicTransformationFlattenedEqs(source::DAE.ElementSource, elt::DAE.Element) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = begin
                  local info::SourceInfo #= the line and column numbers of the equations and algorithms this element came from =#
                  local typeLst::List{Absyn.Path} #= the absyn type of the element =#
                  local partOfLst::List{Absyn.Within} #= the models this element came from =#
                  local instanceOpt::Prefix.ComponentPrefix #= the instance this element is part of =#
                  local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}} #= this element came from this connect =#
                  local operations::List{DAE.SymbolicOperation}
                  local h1::DAE.Exp
                  local t1::DAE.Exp
                  local t2::DAE.Exp
                  local comment::List{SCode.Comment}
                  local scode::SCode.EEquation
                  local elts::List{DAE.Element}
                @match (source, elt) begin
                  (DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, DAE.FLATTEN(scode, NONE()) <| operations, comment), _)  => begin
                    DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, _cons(DAE.FLATTEN(scode, SOME(elt)), operations), comment)
                  end

                  (DAE.SOURCE(info = info), _)  => begin
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list("Tried to add the flattened elements to the list of operations, but did not find the SCode equation"), info)
                    fail()
                  end
                end
              end
          source
        end

        function addSymbolicTransformationSubstitutionLst(add::List{<:Bool}, source::DAE.ElementSource, explst1::List{<:DAE.Exp}, explst2::List{<:DAE.Exp}) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = begin
                  local brest::List{Bool}
                  local rexplst1::List{DAE.Exp}
                  local rexplst2::List{DAE.Exp}
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                @match (add, explst1, explst2) begin
                  ( nil(), _, _)  => begin
                    source
                  end

                  (true <| brest, exp1 <| rexplst1, exp2 <| rexplst2)  => begin
                      source = addSymbolicTransformationSubstitution(true, source, exp1, exp2)
                    addSymbolicTransformationSubstitutionLst(brest, source, rexplst1, rexplst2)
                  end

                  (false <| brest, _ <| rexplst1, _ <| rexplst2)  => begin
                    addSymbolicTransformationSubstitutionLst(brest, source, rexplst1, rexplst2)
                  end
                end
              end
          source
        end

        function addSymbolicTransformationSubstitution(add::Bool, source::DAE.ElementSource, exp1::DAE.Exp, exp2::DAE.Exp) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = condAddSymbolicTransformation(add, source, DAE.SUBSTITUTION(list(exp2), exp1))
          source
        end

        function addSymbolicTransformationSimplifyLst(add::List{<:Bool}, source::DAE.ElementSource, explst1::List{<:DAE.Exp}, explst2::List{<:DAE.Exp}) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = begin
                  local brest::List{Bool}
                  local rexplst1::List{DAE.Exp}
                  local rexplst2::List{DAE.Exp}
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                @match (add, explst1, explst2) begin
                  ( nil(), _, _)  => begin
                    source
                  end

                  (true <| brest, exp1 <| rexplst1, exp2 <| rexplst2)  => begin
                      source = addSymbolicTransformation(source, DAE.SIMPLIFY(DAE.PARTIAL_EQUATION(exp1), DAE.PARTIAL_EQUATION(exp2)))
                    addSymbolicTransformationSimplifyLst(brest, source, rexplst1, rexplst2)
                  end

                  (false <| brest, _ <| rexplst1, _ <| rexplst2)  => begin
                    addSymbolicTransformationSimplifyLst(brest, source, rexplst1, rexplst2)
                  end
                end
              end
          source
        end

        function addSymbolicTransformationSimplify(add::Bool, source::DAE.ElementSource, exp1::DAE.EquationExp, exp2::DAE.EquationExp) ::DAE.ElementSource


              if ! Flags.isSet(Flags.INFO_XML_OPERATIONS)
                return source
              end
              source = condAddSymbolicTransformation(add, source, DAE.SIMPLIFY(exp1, exp2))
          source
        end

        function getAssertCond(stmt::DAE.Statement) ::DAE.Exp
              local cond::DAE.Exp

              @match DAE.STMT_ASSERT(cond = cond) = stmt
          cond
        end

        function addSymbolicTransformationSolve(add::Bool, source::DAE.ElementSource, cr::DAE.ComponentRef, exp1::DAE.Exp, exp2::DAE.Exp, exp::DAE.Exp, asserts::List{<:DAE.Statement}) ::DAE.ElementSource


              local op::DAE.SymbolicOperation
              local op1::DAE.SymbolicOperation
              local op2::DAE.SymbolicOperation

              if ! (add && Flags.isSet(Flags.INFO_XML_OPERATIONS))
                return source
              end
              op1 = DAE.SOLVE(cr, exp1, exp2, exp, list(getAssertCond(ass) for ass in asserts))
              op2 = DAE.SOLVED(cr, exp2) #= If it was already on solved form =#
              op = if CrefForHashTable.expEqual(exp2, exp)
                    op2
                  else
                    op1
                  end
              source = addSymbolicTransformation(source, op)
          source
        end

        function getSymbolicTransformations(source::DAE.ElementSource) ::List{DAE.SymbolicOperation}
              local ops::List{DAE.SymbolicOperation}

              ops = source.operations
          ops
        end

        function getElementSource(element::DAE.Element) ::DAE.ElementSource
              local source::DAE.ElementSource

              source = begin
                @match element begin
                  DAE.VAR(__)  => begin
                    element.source
                  end

                  DAE.DEFINE(__)  => begin
                    element.source
                  end

                  DAE.INITIALDEFINE(__)  => begin
                    element.source
                  end

                  DAE.EQUATION(__)  => begin
                    element.source
                  end

                  DAE.EQUEQUATION(__)  => begin
                    element.source
                  end

                  DAE.ARRAY_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.INITIAL_ARRAY_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.COMPLEX_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.WHEN_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.IF_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.INITIAL_IF_EQUATION(__)  => begin
                    element.source
                  end

                  DAE.INITIALEQUATION(__)  => begin
                    element.source
                  end

                  DAE.ALGORITHM(__)  => begin
                    element.source
                  end

                  DAE.INITIALALGORITHM(__)  => begin
                    element.source
                  end

                  DAE.COMP(__)  => begin
                    element.source
                  end

                  DAE.EXTOBJECTCLASS(__)  => begin
                    element.source
                  end

                  DAE.ASSERT(__)  => begin
                    element.source
                  end

                  DAE.INITIAL_ASSERT(__)  => begin
                    element.source
                  end

                  DAE.TERMINATE(__)  => begin
                    element.source
                  end

                  DAE.INITIAL_TERMINATE(__)  => begin
                    element.source
                  end

                  DAE.REINIT(__)  => begin
                    element.source
                  end

                  DAE.NORETCALL(__)  => begin
                    element.source
                  end

                  DAE.CONSTRAINT(__)  => begin
                    element.source
                  end

                  DAE.INITIAL_NORETCALL(__)  => begin
                    element.source
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("ElementSource.getElementSource failed: Element does not have a source"))
                      fail()
                  end
                end
              end
          source
        end

         #= Returns the element source associated with a statement. =#
        function getStatementSource(stmt::DAE.Statement) ::DAE.ElementSource
              local source::DAE.ElementSource

              source = begin
                @match stmt begin
                  DAE.STMT_ASSIGN(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_TUPLE_ASSIGN(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_ASSIGN_ARR(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_IF(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_FOR(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_PARFOR(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_WHILE(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_WHEN(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_ASSERT(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_TERMINATE(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_REINIT(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_NORETCALL(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_RETURN(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_BREAK(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_ARRAY_INIT(__)  => begin
                    stmt.source
                  end

                  DAE.STMT_FAILURE(__)  => begin
                    stmt.source
                  end
                end
              end
          source
        end

         #= Gets the file information associated with an element.
        If there are several candidates, select the first one. =#
        function getElementSourceFileInfo(source::DAE.ElementSource) ::SourceInfo
              local info::SourceInfo

              info = source.info
          info
        end

        getInfo = getElementSourceFileInfo

         #= @author: adrpo
         retrieves the paths from the DAE.ElementSource.SOURCE.typeLst =#
        function getElementSourceTypes(source::DAE.ElementSource #= the source of the element =#) ::List{Absyn.Path}
              local pathLst::List{Absyn.Path}

              pathLst = source.typeLst
          pathLst
        end

         #= @author: adrpo
         retrieves the paths from the DAE.ElementSource.SOURCE.instanceOpt =#
        function getElementSourceInstances(source::DAE.ElementSource #= the source of the element =#) ::Prefix.ComponentPrefix
              local instanceOpt::Prefix.ComponentPrefix

              instanceOpt = source.instance
          instanceOpt
        end

         #= @author: adrpo
         retrieves the paths from the DAE.ElementSource.SOURCE.connectEquationOptLst =#
        function getElementSourceConnects(source::DAE.ElementSource #= the source of the element =#) ::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
              local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}

              connectEquationOptLst = source.connectEquationOptLst
          connectEquationOptLst
        end

         #= @author: adrpo
         retrieves the withins from the DAE.ElementSource.SOURCE.partOfLst =#
        function getElementSourcePartOfs(source::DAE.ElementSource #= the source of the element =#) ::List{Absyn.Within}
              local withinLst::List{Absyn.Within}

              withinLst = source.partOfLst
          withinLst
        end

        function addElementSourcePartOf(source::DAE.ElementSource, withinPath::Absyn.Within) ::DAE.ElementSource


              if ! (Flags.isSet(Flags.INFO_XML_OPERATIONS) || Flags.isSet(Flags.VISUAL_XML))
                return source
              end
              source.partOfLst = _cons(withinPath, source.partOfLst)
          source
        end

        function addElementSourcePartOfOpt(source::DAE.ElementSource, classPathOpt::Option{<:Absyn.Path}) ::DAE.ElementSource


              if ! (Flags.isSet(Flags.INFO_XML_OPERATIONS) || Flags.isSet(Flags.VISUAL_XML))
                return source
              end
              source = begin
                  local classPath::Absyn.Path
                   #=  a top level
                   =#
                @match (source, classPathOpt) begin
                  (_, NONE())  => begin
                    source
                  end

                  (_, SOME(classPath))  => begin
                    addElementSourcePartOf(source, Absyn.WITHIN(classPath))
                  end
                end
              end
          source
        end

        function addElementSourceFileInfo(source::DAE.ElementSource, fileInfo::SourceInfo) ::DAE.ElementSource
              local outSource::DAE.ElementSource = source

              outSource.info = fileInfo
          outSource
        end

        function addElementSourceConnect(inSource::DAE.ElementSource, connectEquationOpt::Tuple{<:DAE.ComponentRef, DAE.ComponentRef}) ::DAE.ElementSource
              local outSource::DAE.ElementSource

              outSource = begin
                  local info::SourceInfo #= the line and column numbers of the equations and algorithms this element came from =#
                  local partOfLst::List{Absyn.Within} #= the models this element came from =#
                  local instanceOpt::Prefix.ComponentPrefix #= the instance this element is part of =#
                  local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}} #= this element came from this connect =#
                  local typeLst::List{Absyn.Path} #= the classes where the type of the element is defined =#
                  local operations::List{DAE.SymbolicOperation}
                  local comment::List{SCode.Comment}
                   #=  a top level
                   =#
                @match inSource begin
                  DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, comment)  => begin
                    DAE.SOURCE(info, partOfLst, instanceOpt, _cons(connectEquationOpt, connectEquationOptLst), typeLst, operations, comment)
                  end
                end
              end
          outSource
        end

        function addElementSourceType(source::DAE.ElementSource, classPath::Absyn.Path) ::DAE.ElementSource


              if ! (Flags.isSet(Flags.INFO_XML_OPERATIONS) || Flags.isSet(Flags.VISUAL_XML))
                return source
              end
              source = begin
                  local info::SourceInfo #= the line and column numbers of the equations and algorithms this element came from =#
                  local typeLst::List{Absyn.Path} #= the absyn type of the element =#
                  local partOfLst::List{Absyn.Within} #= the models this element came from =#
                  local instanceOpt::Prefix.ComponentPrefix #= the instance this element is part of =#
                  local connectEquationOptLst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}} #= this element came from this connect =#
                  local operations::List{DAE.SymbolicOperation}
                  local comment::List{SCode.Comment}
                @match (source, classPath) begin
                  (DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, typeLst, operations, comment), _)  => begin
                    DAE.SOURCE(info, partOfLst, instanceOpt, connectEquationOptLst, _cons(classPath, typeLst), operations, comment)
                  end
                end
              end
          source
        end

        function addElementSourceInstanceOpt(source::DAE.ElementSource, instanceOpt::Prefix.ComponentPrefix) ::DAE.ElementSource


              () = begin
                @match (source, instanceOpt) begin
                  (_, Prefix.NOCOMPPRE(__))  => begin
                    ()
                  end

                  (DAE.SOURCE(__), _)  => begin
                       #=  a NONE() means top level (equivalent to NO_PRE, SOME(cref) means subcomponent
                       =#
                      source.instance = instanceOpt
                    ()
                  end
                end
              end
          source
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
