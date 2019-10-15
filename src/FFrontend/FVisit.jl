  module FVisit 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    FuncTypeType_aToString = Function

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
         #=  public imports
         =#

        import FCore
        import FNode
         #=  protected imports
         =#

        import ListUtil
        import Error

        Id = FCore.Id 
        Seq = FCore.Seq 
        Next = FCore.Next 
        Node = FCore.Node 
        Ref = FCore.MMRef 
        Data = FCore.Data 
        Visit = FCore.Visit 
        VAvlTree = FCore.VAvlTree 
        Visited = FCore.Visited 
        AvlTree = FCore.VAvlTree 
        AvlKey = FCore.VAvlKey 
        AvlValue = FCore.VAvlValue 
        AvlTreeValue = FCore.VAvlTreeValue 
         const emptyVisited = FCore.V(FCore.emptyVAvlTree, FCore.firstId)::Visited

         #= make a new visited tree =#
        function new() ::Visited 
              local visited::Visited

              visited = emptyVisited
          visited
        end

         #= reset visited information =#
        function reset(inVisited::Visited) ::Visited 
              local visited::Visited

              visited = new()
          visited
        end

        function next(inVisited::Visited) ::Tuple{Visited, Next} 
              local next::Next
              local outVisited::Visited

              local v::VAvlTree
              local n::Next

              @match FCore.V(v, n) = inVisited
              next = n
              n = FCore.next(n)
              outVisited = FCore.V(v, n)
          (outVisited, next)
        end

         #= @autor: adrpo
         check if a node was visited =#
        function visited(inVisited::Visited, inRef::Ref) ::Bool 
              local b::Bool

              b = begin
                  local seq::Seq
                  local a::AvlTree
                  local id::Id
                   #=  there
                   =#
                @matchcontinue (inVisited, inRef) begin
                  (FCore.V(tree = a), _)  => begin
                      _ = FNode.id(FNode.fromRef(inRef))
                      _ = avlTreeGet(a, FNode.id(FNode.fromRef(inRef)))
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  not there
               =#
          b
        end

        function seq(v::Visit) ::Seq 
              local s::Seq

              @match FCore.VN(seq = s) = v
          s
        end

        function ref(v::Visit) ::Ref 
              local r::Ref

              @match FCore.VN(ref = r) = v
          r
        end

        function tree(v::Visited) ::AvlTree 
              local a::AvlTree

              @match FCore.V(tree = a) = v
          a
        end

         #= @autor: adrpo
         add the node to visited =#
        function visit(inVisited::Visited, inRef::Ref) ::Visited 
              local outVisited::Visited

              outVisited = begin
                  local s::Seq
                  local n::Next
                  local a::AvlTree
                  local v::Visit
                  local id::Id
                   #=  already there, something's fishy!
                   =#
                @matchcontinue (inVisited, inRef) begin
                  (_, _)  => begin
                      _ = FNode.id(FNode.fromRef(inRef))
                      v = avlTreeGet(tree(inVisited), FNode.id(FNode.fromRef(inRef)))
                      print("Already visited: " + FNode.toStr(FNode.fromRef(inRef)) + " seq: " + intString(seq(v)) + "\\n")
                    fail()
                  end
                  
                  (FCore.V(a, _), _)  => begin
                      id = FNode.id(FNode.fromRef(inRef))
                      @shouldFail _ = avlTreeGet(tree(inVisited), id)
                      @match (FCore.V(next = n), s) = next(inVisited)
                      a = avlTreeAdd(a, id, FCore.VN(inRef, s))
                      outVisited = FCore.V(a, n)
                    outVisited
                  end
                end
              end
          outVisited
        end

         #=  ************************ AVL Tree implementation ***************************
         =#
         #=  ************************ AVL Tree implementation ***************************
         =#
         #=  ************************ AVL Tree implementation ***************************
         =#
         #=  ************************ AVL Tree implementation ***************************
         =#

         #= compare 2 keys =#
        function keyCompare(k1::AvlKey, k2::AvlKey) ::ModelicaInteger 
              local i::ModelicaInteger

              i = if intGt(k1, k2)
                    1
                  else
                    if intLt(k1, k2)
                          -1
                        else
                          0
                        end
                  end
          i
        end

         #= prints a key to a string =#
        function keyStr(k::AvlKey) ::String 
              local str::String

              str = intString(k)
          str
        end

         #= prints a Value to a string =#
        function valueStr(v::AvlValue) ::String 
              local str::String

              str = begin
                  local seq::ModelicaInteger
                @match v begin
                  FCore.VN(seq = seq)  => begin
                    intString(seq)
                  end
                end
              end
          str
        end

         #= /* Generic Code below */ =#

         #= Return an empty tree =#
        function avlTreeNew() ::AvlTree 
              local tree::AvlTree

              tree = FCore.emptyVAvlTree
          tree
        end

         #= Help function to avlTreeAdd. =#
        function avlTreeAdd(inAvlTree::AvlTree, inKey::AvlKey, inValue::AvlValue) ::AvlTree 
              local outAvlTree::AvlTree

              outAvlTree = begin
                  local key::AvlKey
                  local rkey::AvlKey
                  local value::AvlValue
                   #=  empty tree
                   =#
                @match (inAvlTree, inKey, inValue) begin
                  (FCore.VAVLTREENODE(value = NONE(), left = NONE(), right = NONE()), key, value)  => begin
                    FCore.VAVLTREENODE(SOME(FCore.VAVLTREEVALUE(key, value)), 1, NONE(), NONE())
                  end
                  
                  (FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(key = rkey))), key, value)  => begin
                    balance(avlTreeAdd2(inAvlTree, keyCompare(key, rkey), key, value))
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Env.avlTreeAdd failed"))
                      fail()
                  end
                end
              end
          outAvlTree
        end

         #= Help function to avlTreeAdd. =#
        function avlTreeAdd2(inAvlTree::AvlTree, keyComp::ModelicaInteger #= 0=get value from current node, 1=search right subtree, -1=search left subtree =#, inKey::AvlKey, inValue::AvlValue) ::AvlTree 
              local outAvlTree::AvlTree

              outAvlTree = begin
                  local key::AvlKey
                  local rkey::AvlKey
                  local value::AvlValue
                  local left::Option{AvlTree}
                  local right::Option{AvlTree}
                  local h::ModelicaInteger
                  local t_1::AvlTree
                  local t::AvlTree
                  local oval::Option{AvlTreeValue}
                   #= /*/ Don't allow replacing of nodes.
                      case (_, 0, key, _)
                        equation
                          info = getItemInfo(inValue);
                          Error.addSourceMessage(Error.DOUBLE_DECLARATION_OF_ELEMENTS,
                            {inKey}, info);
                        then
                          fail();*/ =#
                   #=  replace this node
                   =#
                @match (inAvlTree, keyComp, inKey, inValue) begin
                  (FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(key = rkey)), height = h, left = left, right = right), 0, _, value)  => begin
                    FCore.VAVLTREENODE(SOME(FCore.VAVLTREEVALUE(rkey, value)), h, left, right)
                  end
                  
                  (FCore.VAVLTREENODE(value = oval, height = h, left = left, right = right), 1, key, value)  => begin
                      t = createEmptyAvlIfNone(right)
                      t_1 = avlTreeAdd(t, key, value)
                    FCore.VAVLTREENODE(oval, h, left, SOME(t_1))
                  end
                  
                  (FCore.VAVLTREENODE(value = oval, height = h, left = left, right = right), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key, value)  => begin
                      t = createEmptyAvlIfNone(left)
                      t_1 = avlTreeAdd(t, key, value)
                    FCore.VAVLTREENODE(oval, h, SOME(t_1), right)
                  end
                end
              end
               #=  inactive for now, but we should check if we don't replace a class with a var or vice-versa!
               =#
               #=  checkValueReplacementCompatible(rval, value);
               =#
               #=  insert to right
               =#
               #=  insert to left subtree
               =#
          outAvlTree
        end

         #= Help function to AvlTreeAdd2 =#
        function createEmptyAvlIfNone(t::Option{<:AvlTree}) ::AvlTree 
              local outT::AvlTree

              outT = begin
                @match t begin
                  NONE()  => begin
                    FCore.VAVLTREENODE(NONE(), 0, NONE(), NONE())
                  end
                  
                  SOME(outT)  => begin
                    outT
                  end
                end
              end
          outT
        end

         #= return the node value =#
        function nodeValue(bt::AvlTree) ::AvlValue 
              local v::AvlValue

              v = begin
                @match bt begin
                  FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(_, v)))  => begin
                    v
                  end
                end
              end
          v
        end

         #= Balances a AvlTree =#
        function balance(inBt::AvlTree) ::AvlTree 
              local outBt::AvlTree

              outBt = begin
                  local d::ModelicaInteger
                  local bt::AvlTree
                @match inBt begin
                  bt  => begin
                      d = differenceInHeight(bt)
                      bt = doBalance(d, bt)
                    bt
                  end
                end
              end
          outBt
        end

         #= perform balance if difference is > 1 or < -1 =#
        function doBalance(difference::ModelicaInteger, inBt::AvlTree) ::AvlTree 
              local outBt::AvlTree

              outBt = begin
                  local bt::AvlTree
                @match (difference, inBt) begin
                  (#= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, bt)  => begin
                    computeHeight(bt)
                  end
                  
                  (0, bt)  => begin
                    computeHeight(bt)
                  end
                  
                  (1, bt)  => begin
                    computeHeight(bt)
                  end
                  
                  (_, bt)  => begin
                      bt = doBalance2(difference < 0, bt)
                    bt
                  end
                end
              end
               #= /* d < -1 or d > 1 */ =#
          outBt
        end

         #= help function to doBalance =#
        function doBalance2(differenceIsNegative::Bool, inBt::AvlTree) ::AvlTree 
              local outBt::AvlTree

              outBt = begin
                  local bt::AvlTree
                @match (differenceIsNegative, inBt) begin
                  (true, bt)  => begin
                      bt = doBalance3(bt)
                      bt = rotateLeft(bt)
                    bt
                  end
                  
                  (false, bt)  => begin
                      bt = doBalance4(bt)
                      bt = rotateRight(bt)
                    bt
                  end
                end
              end
          outBt
        end

         #= help function to doBalance2 =#
        function doBalance3(inBt::AvlTree) ::AvlTree 
              local outBt::AvlTree

              outBt = begin
                  local rr::AvlTree
                  local bt::AvlTree
                @matchcontinue inBt begin
                  bt  => begin
                      @match true = differenceInHeight(getOption(rightNode(bt))) > 0
                      rr = rotateRight(getOption(rightNode(bt)))
                      bt = setRight(bt, SOME(rr))
                    bt
                  end
                  
                  _  => begin
                      inBt
                  end
                end
              end
          outBt
        end

         #= help function to doBalance2 =#
        function doBalance4(inBt::AvlTree) ::AvlTree 
              local outBt::AvlTree

              outBt = begin
                  local rl::AvlTree
                  local bt::AvlTree
                @matchcontinue inBt begin
                  bt  => begin
                      @match true = differenceInHeight(getOption(leftNode(bt))) < 0
                      rl = rotateLeft(getOption(leftNode(bt)))
                      bt = setLeft(bt, SOME(rl))
                    bt
                  end
                  
                  _  => begin
                      inBt
                  end
                end
              end
          outBt
        end

         #= set right treenode =#
        function setRight(node::AvlTree, right::Option{<:AvlTree}) ::AvlTree 
              local outNode::AvlTree

              outNode = begin
                  local value::Option{AvlTreeValue}
                  local l::Option{AvlTree}
                  local r::Option{AvlTree}
                  local height::ModelicaInteger
                @match (node, right) begin
                  (FCore.VAVLTREENODE(value, height, l, _), _)  => begin
                    FCore.VAVLTREENODE(value, height, l, right)
                  end
                end
              end
          outNode
        end

         #= set left treenode =#
        function setLeft(node::AvlTree, left::Option{<:AvlTree}) ::AvlTree 
              local outNode::AvlTree

              outNode = begin
                  local value::Option{AvlTreeValue}
                  local l::Option{AvlTree}
                  local r::Option{AvlTree}
                  local height::ModelicaInteger
                @match (node, left) begin
                  (FCore.VAVLTREENODE(value, height, _, r), _)  => begin
                    FCore.VAVLTREENODE(value, height, left, r)
                  end
                end
              end
          outNode
        end

         #= Retrieve the left subnode =#
        function leftNode(node::AvlTree) ::Option{AvlTree} 
              local subNode::Option{AvlTree}

              subNode = begin
                @match node begin
                  FCore.VAVLTREENODE(left = subNode)  => begin
                    subNode
                  end
                end
              end
          subNode
        end

         #= Retrieve the right subnode =#
        function rightNode(node::AvlTree) ::Option{AvlTree} 
              local subNode::Option{AvlTree}

              subNode = begin
                @match node begin
                  FCore.VAVLTREENODE(right = subNode)  => begin
                    subNode
                  end
                end
              end
          subNode
        end

         #= help function to balance =#
        function exchangeLeft(inNode::AvlTree, inParent::AvlTree) ::AvlTree 
              local outParent::AvlTree #= updated parent =#

              outParent = begin
                  local bt::AvlTree
                  local node::AvlTree
                  local parent::AvlTree
                @match (inNode, inParent) begin
                  (node, parent)  => begin
                      parent = setRight(parent, leftNode(node))
                      parent = balance(parent)
                      node = setLeft(node, SOME(parent))
                      bt = balance(node)
                    bt
                  end
                end
              end
          outParent #= updated parent =#
        end

         #= help function to balance =#
        function exchangeRight(inNode::AvlTree, inParent::AvlTree) ::AvlTree 
              local outParent::AvlTree #= updated parent =#

              outParent = begin
                  local bt::AvlTree
                  local node::AvlTree
                  local parent::AvlTree
                @match (inNode, inParent) begin
                  (node, parent)  => begin
                      parent = setLeft(parent, rightNode(node))
                      parent = balance(parent)
                      node = setRight(node, SOME(parent))
                      bt = balance(node)
                    bt
                  end
                end
              end
          outParent #= updated parent =#
        end

         #= help function to balance =#
        function rotateLeft(node::AvlTree) ::AvlTree 
              local outNode::AvlTree #= updated node =#

              outNode = exchangeLeft(getOption(rightNode(node)), node)
          outNode #= updated node =#
        end

         #= Retrieve the value of an option =#
        function getOption(opt::Option{<:T}) ::T 
              local val::T

              val = begin
                @match opt begin
                  SOME(val)  => begin
                    val
                  end
                end
              end
          val
        end

         #= help function to balance =#
        function rotateRight(node::AvlTree) ::AvlTree 
              local outNode::AvlTree #= updated node =#

              outNode = exchangeRight(getOption(leftNode(node)), node)
          outNode #= updated node =#
        end

         #= help function to balance, calculates the difference in height
        between left and right child =#
        function differenceInHeight(node::AvlTree) ::ModelicaInteger 
              local diff::ModelicaInteger

              diff = begin
                  local lh::ModelicaInteger
                  local rh::ModelicaInteger
                  local l::Option{AvlTree}
                  local r::Option{AvlTree}
                @match node begin
                  FCore.VAVLTREENODE(left = l, right = r)  => begin
                      lh = getHeight(l)
                      rh = getHeight(r)
                    lh - rh
                  end
                end
              end
          diff
        end

         #= Get a value from the binary tree given a key. =#
        function avlTreeGet(inAvlTree::AvlTree, inKey::AvlKey) ::AvlValue 
              local outValue::AvlValue

              outValue = begin
                  local rkey::AvlKey
                  local key::AvlKey
                @match (inAvlTree, inKey) begin
                  (FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(key = rkey))), key)  => begin
                    avlTreeGet2(inAvlTree, keyCompare(key, rkey), key)
                  end
                end
              end
          outValue
        end

         #= Get a value from the binary tree given a key. =#
        function avlTreeGet2(inAvlTree::AvlTree, keyComp::ModelicaInteger #= 0=get value from current node, 1=search right subtree, -1=search left subtree =#, inKey::AvlKey) ::AvlValue 
              local outValue::AvlValue

              outValue = begin
                  local key::AvlKey
                  local rval::AvlValue
                  local left::AvlTree
                  local right::AvlTree
                   #=  hash func Search to the right
                   =#
                @match (inAvlTree, keyComp, inKey) begin
                  (FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(value = rval))), 0, _)  => begin
                    rval
                  end
                  
                  (FCore.VAVLTREENODE(right = SOME(right)), 1, key)  => begin
                    avlTreeGet(right, key)
                  end
                  
                  (FCore.VAVLTREENODE(left = SOME(left)), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key)  => begin
                    avlTreeGet(left, key)
                  end
                end
              end
               #=  search to the right
               =#
               #=  search to the left
               =#
          outValue
        end

         #= Retrieve the string from a string option.
          If NONE() return empty string. =#
        function getOptionStr(inTypeAOption::Option{<:Type_a}, inFuncTypeTypeAToString::FuncTypeType_aToString) ::String 
              local outString::String

              outString = begin
                  local str::String
                  local a::Type_a
                  local r::FuncTypeType_aToString
                @match (inTypeAOption, inFuncTypeTypeAToString) begin
                  (SOME(a), r)  => begin
                      str = r(a)
                    str
                  end
                  
                  (NONE(), _)  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= 
          Prints the avl tree to a string =#
        function printAvlTreeStr(inAvlTree::AvlTree) ::String 
              local outString::String

              outString = begin
                  local rkey::AvlKey
                  local s2::String
                  local s3::String
                  local res::String
                  local rval::AvlValue
                  local l::Option{AvlTree}
                  local r::Option{AvlTree}
                  local h::ModelicaInteger
                @match inAvlTree begin
                  FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(_, rval)), left = l, right = r)  => begin
                      s2 = getOptionStr(l, printAvlTreeStr)
                      s3 = getOptionStr(r, printAvlTreeStr)
                      res = "\\n" + valueStr(rval) + ",  " + (if stringEq(s2, "")
                            ""
                          else
                            s2 + ", "
                          end) + s3
                    res
                  end
                  
                  FCore.VAVLTREENODE(value = NONE(), left = l, right = r)  => begin
                      s2 = getOptionStr(l, printAvlTreeStr)
                      s3 = getOptionStr(r, printAvlTreeStr)
                      res = (if stringEq(s2, "")
                            ""
                          else
                            s2 + ", "
                          end) + s3
                    res
                  end
                end
              end
          outString
        end

         #= compute the heigth of the AvlTree and store in the node info =#
        function computeHeight(bt::AvlTree) ::AvlTree 
              local outBt::AvlTree

              outBt = begin
                  local l::Option{AvlTree}
                  local r::Option{AvlTree}
                  local v::Option{AvlTreeValue}
                  local hl::ModelicaInteger
                  local hr::ModelicaInteger
                  local height::ModelicaInteger
                @match bt begin
                  FCore.VAVLTREENODE(value = v && SOME(_), left = l, right = r)  => begin
                      hl = getHeight(l)
                      hr = getHeight(r)
                      height = intMax(hl, hr) + 1
                    FCore.VAVLTREENODE(v, height, l, r)
                  end
                end
              end
          outBt
        end

         #= Retrieve the height of a node =#
        function getHeight(bt::Option{<:AvlTree}) ::ModelicaInteger 
              local height::ModelicaInteger

              height = begin
                @match bt begin
                  NONE()  => begin
                    0
                  end
                  
                  SOME(FCore.VAVLTREENODE(height = height))  => begin
                    height
                  end
                end
              end
          height
        end

        function printAvlTreeStrPP(inTree::AvlTree) ::String 
              local outString::String

              outString = printAvlTreeStrPP2(SOME(inTree), "")
          outString
        end

        function printAvlTreeStrPP2(inTree::Option{<:AvlTree}, inIndent::String) ::String 
              local outString::String

              outString = begin
                  local rkey::AvlKey
                  local l::Option{AvlTree}
                  local r::Option{AvlTree}
                  local s1::String
                  local s2::String
                  local res::String
                  local indent::String
                @match (inTree, inIndent) begin
                  (NONE(), _)  => begin
                    ""
                  end
                  
                  (SOME(FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(key = rkey)), left = l, right = r)), _)  => begin
                      indent = inIndent + "  "
                      s1 = printAvlTreeStrPP2(l, indent)
                      s2 = printAvlTreeStrPP2(r, indent)
                      res = "\\n" + inIndent + keyStr(rkey) + s1 + s2
                    res
                  end
                  
                  (SOME(FCore.VAVLTREENODE(value = NONE(), left = l, right = r)), _)  => begin
                      indent = inIndent + "  "
                      s1 = printAvlTreeStrPP2(l, indent)
                      s2 = printAvlTreeStrPP2(r, indent)
                      res = "\\n" + s1 + s2
                    res
                  end
                end
              end
          outString
        end

         #= Replaces the value of an already existing node in the tree with a new value. =#
        function avlTreeReplace(inAvlTree::AvlTree, inKey::AvlKey, inValue::AvlValue) ::AvlTree 
              local outAvlTree::AvlTree

              outAvlTree = begin
                  local key::AvlKey
                  local rkey::AvlKey
                  local value::AvlValue
                @match (inAvlTree, inKey, inValue) begin
                  (FCore.VAVLTREENODE(value = SOME(FCore.VAVLTREEVALUE(key = rkey))), key, value)  => begin
                    avlTreeReplace2(inAvlTree, keyCompare(key, rkey), key, value)
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list(getInstanceName() + " failed"))
                      fail()
                  end
                end
              end
          outAvlTree
        end

         #= Helper function to avlTreeReplace. =#
        function avlTreeReplace2(inAvlTree::AvlTree, inKeyComp::ModelicaInteger, inKey::AvlKey, inValue::AvlValue) ::AvlTree 
              local outAvlTree::AvlTree

              outAvlTree = begin
                  local key::AvlKey
                  local value::AvlValue
                  local left::Option{AvlTree}
                  local right::Option{AvlTree}
                  local h::ModelicaInteger
                  local t::AvlTree
                  local oval::Option{AvlTreeValue}
                   #=  Replace this node.
                   =#
                @match (inAvlTree, inKeyComp, inKey, inValue) begin
                  (FCore.VAVLTREENODE(value = SOME(_), height = h, left = left, right = right), 0, key, value)  => begin
                    FCore.VAVLTREENODE(SOME(FCore.VAVLTREEVALUE(key, value)), h, left, right)
                  end
                  
                  (FCore.VAVLTREENODE(value = oval, height = h, left = left, right = right), 1, key, value)  => begin
                      t = createEmptyAvlIfNone(right)
                      t = avlTreeReplace(t, key, value)
                    FCore.VAVLTREENODE(oval, h, left, SOME(t))
                  end
                  
                  (FCore.VAVLTREENODE(value = oval, height = h, left = left, right = right), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key, value)  => begin
                      t = createEmptyAvlIfNone(left)
                      t = avlTreeReplace(t, key, value)
                    FCore.VAVLTREENODE(oval, h, SOME(t), right)
                  end
                end
              end
               #=  Insert into right subtree.
               =#
               #=  Insert into left subtree.
               =#
          outAvlTree
        end

        function getAvlTreeValues(tree::List{<:Option{<:AvlTree}}, acc::List{<:AvlTreeValue}) ::List{AvlTreeValue} 
              local res::List{AvlTreeValue}

              res = begin
                  local value::Option{AvlTreeValue}
                  local left::Option{AvlTree}
                  local right::Option{AvlTree}
                  local rest::List{Option{AvlTree}}
                @match (tree, acc) begin
                  ( nil(), _)  => begin
                    acc
                  end
                  
                  (SOME(FCore.VAVLTREENODE(value = value, left = left, right = right)) <| rest, _)  => begin
                    getAvlTreeValues(_cons(left, _cons(right, rest)), ListUtil.consOption(value, acc))
                  end
                  
                  (NONE() <| rest, _)  => begin
                    getAvlTreeValues(rest, acc)
                  end
                end
              end
          res
        end

        function getAvlValue(inValue::AvlTreeValue) ::AvlValue 
              local res::AvlValue

              res = begin
                @match inValue begin
                  FCore.VAVLTREEVALUE(value = res)  => begin
                    res
                  end
                end
              end
          res
        end

         #=  ************************ END AVL Tree implementation ***************************
         =#
         #=  ************************ END AVL Tree implementation ***************************
         =#
         #=  ************************ END AVL Tree implementation ***************************
         =#
         #=  ************************ END AVL Tree implementation ***************************
         =#

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end