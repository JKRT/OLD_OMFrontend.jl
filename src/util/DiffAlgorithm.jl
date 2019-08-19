  module DiffAlgorithm 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    FunEquals = Function
    FunWhitespace = Function
    ToString = Function
    partialPrintDiff = Function

    FunEquals = Function
    FunWhitespace = Function
    ToString = Function

    FunEquals = Function
    FunWhitespace = Function
    ToString = Function

    FunEquals = Function
    FunWhitespace = Function
    ToString = Function

    FunEquals = Function

    FunEquals = Function

    FunEquals = Function

         #= /*
         * This file is part of OpenModelica.
         *
         * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
         * c/o Linköpings universitet, Department of Computer and Information Science,
         * SE-58183 Linköping, Sweden.
         *
         * All rights reserved.
         *
         * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
         * THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
         * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
         * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
         * ACCORDING TO RECIPIENTS CHOICE.
         *
         * The OpenModelica software and the Open Source Modelica
         * Consortium (OSMC) Public License (OSMC-PL) are obtained
         * from OSMC, either from the above address,
         * from the URLs: http:www.ida.liu.se/projects/OpenModelica or
         * http:www.openmodelica.org, and in the OpenModelica distribution.
         * GNU version 3 is obtained from: http:www.gnu.org/copyleft/gpl.html.
         *
         * This program is distributed WITHOUT ANY WARRANTY; without
         * even the implied warranty of  MERCHANTABILITY or FITNESS
         * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
         * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
         *
         * See the full OSMC Public License conditions for more details.
         *
         */ =#
        import Print

        import MetaModelica.ListUtil
        import System



        function diff(seq1::List{T}, seq2::List{T}, equals::FunEquals, isWhitespace::FunWhitespace, toString::ToString)  where {T}
              local out::List{Tuple{Diff, List{T}}}

              local start1::ModelicaInteger
              local end1::ModelicaInteger
              local start2::ModelicaInteger
              local end2::ModelicaInteger
              local len1::ModelicaInteger
              local len2::ModelicaInteger
              local arr1::Array{T}
              local arr2::Array{T}

              arr1 = listArray(seq1)
              arr2 = listArray(seq2)
              start1 = 1
              start2 = 1
              end1 = arrayLength(arr1)
              end2 = arrayLength(arr2)
              out = diffSeq(arr1, arr2, equals, isWhitespace, toString, start1, end1, start2, end2)
          out
        end



        function printDiffTerminalColor()  
        end

        function printDiffXml()  
        end

        function printActual()  
        end

        function diffSeq(arr1::Array{T}, arr2::Array{T}, equals::FunEquals, isWhitespace::FunWhitespace, toString::ToString, inStart1::ModelicaInteger, inEnd1::ModelicaInteger, inStart2::ModelicaInteger, inEnd2::ModelicaInteger, inPrefixes::List{Tuple{Diff, List{T}}} = nil, inSuffixes::List{Tuple{Diff, List{T}}} = nil)  where {T}
              local out::List{Tuple{Diff, List{T}}}

              local start1::ModelicaInteger = inStart1
              local end1::ModelicaInteger = inEnd1
              local start2::ModelicaInteger = inStart2
              local end2::ModelicaInteger = inEnd2
              local len1::ModelicaInteger
              local len2::ModelicaInteger
              local prefixes::List{Tuple{Diff, List{T}}} = inPrefixes
              local suffixes::List{Tuple{Diff, List{T}}} = inSuffixes

              len1 = end1 - start1 + 1
              len2 = end2 - start2 + 1
               #=  Some of these tricks were inspired by diff-match-patch:
               =#
               #=    https:code.google.com/p/google-diff-match-patch/
               =#
               #=  They do checks that are trivial and optimal, but could significantly
               =#
               #=    slow down the rest of Myer's diff algorithm
               =#
               #=  Check if either sequence is empty. Trivial to diff.
               =#
              if len1 < 1 && len2 < 1
                out = ListUtil.append_reverse(prefixes, suffixes)
                return out
              elseif len1 < 1
                out = ListUtil.append_reverse(prefixes, _cons((Diff.Add, list(arr2[e] for e in start2:end2)), suffixes))
                return out
              elseif len2 < 1
                out = ListUtil.append_reverse(prefixes, _cons((Diff.Delete, list(arr1[e] for e in start1:end1)), suffixes))
                return out
              end
               #=  Note the horrible syntax for short-circuit evaluation
               =#
               #=  Check if the sequences are equal. Trivial diff.
               =#
              if if len1 == len2
                    min(@do_threaded_for equals(e1, e2) (e1, e2) (arr1, arr2))
                  else
                    false
                  end
                out = list((Diff.Equal, list(arr1[e] for e in start1:end1)))
                return out
              end
               #=  trim off common prefix; guaranteed to be a good solution
               =#
              (prefixes, start1, start2) = trimCommonPrefix(arr1, start1, end1, arr2, start2, end2, equals, prefixes)
               #=  trim off common suffix; guaranteed to be a good solution
               =#
              (suffixes, end1, end2) = trimCommonSuffix(arr1, start1, end1, arr2, start2, end2, equals, suffixes)
               #=  Check if anything changed and iterate. A sequence could now be empty.
               =#
              if start1 != inStart1 || start2 != inStart2 || end1 != inEnd1 || end2 != inEnd2
                out = diffSeq(arr1, arr2, equals, isWhitespace, toString, start1, end1, start2, end2, inPrefixes = prefixes, inSuffixes = suffixes)
                return out
              else
                out = begin
                  @matchcontinue () begin
                    ()  => begin
                      onlyAdditions(arr1, arr2, equals, isWhitespace, toString, start1, end1, start2, end2)
                    end
                    
                    ()  => begin
                      onlyRemovals(arr1, arr2, equals, isWhitespace, toString, start1, end1, start2, end2)
                    end
                    
                    _  => begin
                        myersGreedyDiff(arr1, arr2, equals, start1, end1, start2, end2)
                    end
                  end
                end
                out = ListUtil.append_reverse(prefixes, listAppend(out, suffixes))
                return out
              end
               #=  TODO: cleanup
               =#
              fail()
          out
        end

        function addToList(inlst::List{Tuple{Diff, List{T}}}, ind::Diff, inacc::List{T}, newd::Diff, t::T)  where {T}
              local acc::List{T} = inacc
              local d::Diff = newd
              local lst::List{Tuple{Diff, List{T}}} = inlst

              if ind == newd
                acc = _cons(t, acc)
              else
                if ! listEmpty(inacc)
                  lst = _cons((ind, listReverse(acc)), lst)
                end
                acc = list(t)
              end
          (lst, d, acc)
        end

        function endList(inlst::List{Tuple{Diff, List{T}}}, ind::Diff, inacc::List{T})  where {T}
              local lst::List{Tuple{Diff, List{T}}} = inlst

              if ! listEmpty(inacc)
                lst = _cons((ind, listReverse(inacc)), lst)
              end
          lst
        end

        function onlyAdditions(arr1::Array{T}, arr2::Array{T}, equals::FunEquals, isWhitespace::FunWhitespace, toString::ToString, start1::ModelicaInteger, end1::ModelicaInteger, start2::ModelicaInteger, end2::ModelicaInteger)  where {T}
              local out::List{Tuple{Diff, List{T}}}

              local x::ModelicaInteger = 0
              local y::ModelicaInteger = 0
              local d::Diff = Diff.Equal
              local lst::List{T} = nil

              out = nil
               #=  print(\"Try only additions\\n\");
               =#
              while start1 + x <= end1 && start2 + y <= end2
                if equals(arr1[start1 + x], arr2[start2 + y])
                  (out, d, lst) = addToList(out, d, lst, Diff.Equal, arr1[start1 + x])
                  x = x + 1
                  y = y + 1
                elseif isWhitespace(arr1[start1 + x])
                  (out, d, lst) = addToList(out, d, lst, Diff.Delete, arr1[start1 + x])
                  x = x + 1
                else
                  (out, d, lst) = addToList(out, d, lst, Diff.Add, arr2[start2 + y])
                  y = y + 1
                end
              end
               #=  print(\"Try only additions\"+String(x)+\",\"+String(y)+\"\\n\");
               =#
               #=  print(\"1: \" + System.trim(toString(arr1[start1+x]))+\"\\n\");
               =#
               #=  print(\"2: \" + System.trim(toString(arr2[start2+y]))+\"\\n\");
               =#
               #=  print(\"Both equal\\n\");
               =#
               #=  print(\"Deleting: \" + toString(arr1[start1+x])+\"\\n\");
               =#
               #=  print(\"Adding: \" + toString(arr2[start2+y])+\"\\n\");
               =#
              while start1 + x <= end1
                if isWhitespace(arr1[start1 + x])
                  (out, d, lst) = addToList(out, d, lst, Diff.Delete, arr1[start1 + x])
                  x = x + 1
                else
                  fail()
                end
              end
              while start2 + y <= end2
                if isWhitespace(arr2[start2 + y])
                  (out, d, lst) = addToList(out, d, lst, Diff.Add, arr2[start2 + y])
                  y = y + 1
                else
                  fail()
                end
              end
              out = endList(out, d, lst)
               #=  print(\"It is only additions :)\\n\");
               =#
              out = listReverse(out)
          out
        end

        function onlyRemovals(arr1::Array{T}, arr2::Array{T}, equals::FunEquals, isWhitespace::FunWhitespace, toString::ToString, start1::ModelicaInteger, end1::ModelicaInteger, start2::ModelicaInteger, end2::ModelicaInteger)  where {T}
              local out::List{Tuple{Diff, List{T}}}

              local x::ModelicaInteger = 0
              local y::ModelicaInteger = 0
              local d::Diff = Diff.Equal
              local lst::List{T} = nil

              out = nil
               #=  print(\"Try only removals\\n\");
               =#
              while start1 + x <= end1 && start2 + y <= end2
                if equals(arr1[start1 + x], arr2[start2 + y])
                  (out, d, lst) = addToList(out, d, lst, Diff.Equal, arr1[start1 + x])
                  x = x + 1
                  y = y + 1
                elseif isWhitespace(arr2[start2 + y])
                  (out, d, lst) = addToList(out, d, lst, Diff.Add, arr2[start2 + y])
                  y = y + 1
                else
                  (out, d, lst) = addToList(out, d, lst, Diff.Delete, arr1[start1 + x])
                  x = x + 1
                end
              end
               #=  print(\"Try only removals\"+String(x)+\",\"+String(y)+\"\\n\");
               =#
               #=  print(\"1: \" + System.trim(toString(arr1[start1+x]))+\"\\n\");
               =#
               #=  print(\"2: \" + System.trim(toString(arr2[start2+y]))+\"\\n\");
               =#
               #=  print(\"Both equal\\n\");
               =#
               #=  print(\"Deleting: \" + toString(arr1[start1+x])+\"\\n\");
               =#
               #=  print(\"Adding: \" + toString(arr2[start2+y])+\"\\n\");
               =#
              while start1 + x <= end1
                if isWhitespace(arr1[start1 + x])
                  (out, d, lst) = addToList(out, d, lst, Diff.Delete, arr1[start1 + x])
                  x = x + 1
                else
                  fail()
                end
              end
              while start2 + y <= end2
                if isWhitespace(arr2[start2 + y])
                  (out, d, lst) = addToList(out, d, lst, Diff.Add, arr2[start2 + y])
                  y = y + 1
                else
                  fail()
                end
              end
              out = endList(out, d, lst)
               #=  print(\"It is only additions :)\\n\");
               =#
              out = listReverse(out)
          out
        end

        function myersGreedyDiff(arr1::Array{T}, arr2::Array{T}, equals::FunEquals, start1::ModelicaInteger, end1::ModelicaInteger, start2::ModelicaInteger, end2::ModelicaInteger)  where {T}
              local out::List{Tuple{Diff, List{T}}}

              local len1::ModelicaInteger
              local len2::ModelicaInteger
              local maxIter::ModelicaInteger
              local sz::ModelicaInteger
              local middle::ModelicaInteger
              local x::ModelicaInteger
              local y::ModelicaInteger
              local V::Array{ModelicaInteger}
              local paths::Array{List{Tuple{ModelicaInteger, ModelicaInteger}}}
              local prevPath::List{Tuple{ModelicaInteger, ModelicaInteger}}

               #=  Greedy LCS/SES
               =#
              len1 = end1 - start1 + 1
              len2 = end2 - start2 + 1
              maxIter = len1 + len2
              sz = 2 * maxIter + 1
              middle = maxIter + 1
              V = arrayCreate(sz, 0)
              paths = arrayCreate(sz, nil)
              for D in 0:maxIter
                for k in (-D):2:D
                  if k == (-D) || k != D && V[k - 1 + middle] < V[k + 1 + middle]
                    x = V[k + 1 + middle]
                    prevPath = paths[k + 1 + middle]
                  else
                    x = V[k - 1 + middle] + 1
                    prevPath = paths[k - 1 + middle]
                  end
                  y = x - k
                  paths[k + middle] = _cons((x, y), prevPath)
                  while if x < len1 && y < len2
                        equals(arr1[start1 + x], arr2[start2 + y])
                      else
                        false
                      end
                    x = x + 1
                    y = y + 1
                    paths[k + middle] = _cons((x, y), paths[k + middle])
                  end
                  V[k + middle] = x
                  if x >= len1 && y >= len2
                    out = myersGreedyPathToDiff(arr1, arr2, start1, start2, paths[k + middle])
                    return out
                  end
                end
              end
               #=  Length of an SES is D
               =#
              print("myersDiff: This cannot happen")
              fail()
          out
        end

        function myersGreedyPathToDiff(arr1::Array{T}, arr2::Array{T}, start1::ModelicaInteger, start2::ModelicaInteger, paths::List{Tuple{ModelicaInteger, ModelicaInteger}})  where {T}
              local out::List{Tuple{Diff, List{T}}} = nil

              local x1::ModelicaInteger
              local x2::ModelicaInteger
              local y1::ModelicaInteger
              local y2::ModelicaInteger
              local d1::Diff = Diff.Equal
              local d2::Diff = Diff.Equal
              local lst::List{T} = nil
              local t::T

              @match _cons((x2, y2), _) = paths
               #=  starting point
               =#
              for path in listRest(paths)
                (x1, y1) = path
                if x2 - x1 == 1 && y2 - y1 == 1
                  d1 = Diff.Equal
                  t = arr1[start1 + x1]
                elseif x2 - x1 == 1 && y2 == y1
                  d1 = Diff.Delete
                  t = arr1[start1 + x1]
                elseif y2 - y1 == 1 && x2 == x1
                  d1 = Diff.Add
                  t = arr2[start2 + y1]
                else
                  print("myersGreedyPathToDiff: This cannot happen\\n")
                  fail()
                end
                if listEmpty(lst)
                  lst = list(t)
                elseif d1 == d2
                  lst = _cons(t, lst)
                else
                  out = _cons((d2, lst), out)
                  lst = list(t)
                end
                d2 = d1
                x2 = x1
                y2 = y1
              end
               #=  Diagonal
               =#
               #=  Horizontal is addition
               =#
               #=  Vertical is deletion
               =#
               #=  Else is WTF?
               =#
              if ! listEmpty(lst)
                out = _cons((d2, lst), out)
              end
          out
        end

        function trimCommonPrefix(arr1::Array{T}, inStart1::ModelicaInteger, end1::ModelicaInteger, arr2::Array{T}, inStart2::ModelicaInteger, end2::ModelicaInteger, equals::FunEquals, acc::List{Tuple{Diff, List{T}}})  where {T}
              local start1::ModelicaInteger = inStart1
              local start2::ModelicaInteger = inStart2
              local prefixes::List{Tuple{Diff, List{T}}} = acc

              local lst::List{T} = nil

              while if start1 <= end1 && start2 <= end2
                    equals(arr1[start1], arr2[start2])
                  else
                    false
                  end
                lst = _cons(arr1[start1], lst)
                start1 = start1 + 1
                start2 = start2 + 1
              end
              if ! listEmpty(lst)
                prefixes = _cons((Diff.Equal, listReverse(lst)), prefixes)
              end
          (prefixes, start1, start2)
        end

        function trimCommonSuffix(arr1::Array{T}, start1::ModelicaInteger, inEnd1::ModelicaInteger, arr2::Array{T}, start2::ModelicaInteger, inEnd2::ModelicaInteger, equals::FunEquals, acc::List{Tuple{Diff, List{T}}})  where {T}
              local end1::ModelicaInteger = inEnd1
              local end2::ModelicaInteger = inEnd2
              local suffixes::List{Tuple{Diff, List{T}}} = acc

              local lst::List{T} = nil

              while if start1 <= end1 && start2 <= end2
                    equals(arr1[end1], arr2[end2])
                  else
                    false
                  end
                lst = _cons(arr1[end1], lst)
                end1 = end1 - 1
                end2 = end2 - 1
              end
              if ! listEmpty(lst)
                suffixes = _cons((Diff.Equal, lst), suffixes)
              end
          (suffixes, end1, end2)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end