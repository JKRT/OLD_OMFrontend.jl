  module AvlTree 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    FuncTypeKeyToStr = Function
    FuncTypeValToStr = Function
    FuncTypeItemUpdateCheck = Function
    FuncTypeKeyCompare = Function
    @UniontypeDecl Tree 
    @UniontypeDecl Node 
    @UniontypeDecl Item 

         #= /*
         * This file is part of OpenModelica.
         *
         * Copyright (c) 1998-CurrentYear, Linköping University,
         * Department of Computer and Information Science,
         * SE-58183 Linköping, Sweden.
         *
         * All rights reserved.
         *
         * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3
         * AND THIS OSMC PUBLIC LICENSE (OSMC-PL).
         * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES RECIPIENT'S
         * ACCEPTANCE OF THE OSMC PUBLIC LICENSE.
         *
         * The OpenModelica software and the Open Source Modelica
         * Consortium (OSMC) Public License (OSMC-PL) are obtained
         * from Linköping University, either from the above address,
         * from the URLs: http:www.ida.liu.se/projects/OpenModelica or
         * http:www.openmodelica.org, and in the OpenModelica distribution.
         * GNU version 3 is obtained from: http:www.gnu.org/copyleft/gpl.html.
         *
         * This program is distributed WITHOUT ANY WARRANTY; without
         * even the implied warranty of  MERCHANTABILITY or FITNESS
         * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
         * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS
         * OF OSMC-PL.
         *
         * See the full OSMC Public License conditions for more details.
         *
         */ =#

        Key = Any 
        Val = Any 









          #= a tree is a node and two optional printing functions =#
         @Uniontype Tree begin
              @Record TREE begin

                       root::Node{Key, Val}
                       keyCompareFunc #= function to compare keys, should return -1, 0, 1 ONLY! =#::FuncTypeKeyCompare
                       keyStrFuncOpt #= optional function for printing Key =#::Option{FuncTypeKeyToStr}
                       valStrFuncOpt #= optional function for printing Val =#::Option{FuncTypeValToStr}
                       updateCheckFuncOpt #= optional function for reporting error on an update of the same item
                              if this function is NONE() then updates of items with the same key is allowed!
                              this function gets the new item and the old item for easy reporting,
                              and should return:
                              - true if update is allowed
                              - false if update should not be done
                              - should print an error message and fail if it wants to fail the update =#::Option{FuncTypeItemUpdateCheck}
                       name #= a name for this tree so you know which one it is if you have more =#::String
              end
         end

          #= The binary tree data structure =#
         @Uniontype Node begin
              @Record NODE begin

                       item #= Val =#::Item{Key, Val}
                       height #= height of tree, used for balancing =#::ModelicaInteger
                       left #= left subtree =#::Node{Key, Val}
                       right #= right subtree =#::Node{Key, Val}
              end

              @Record NO_NODE begin

              end
         end

          #= Each node in the binary tree can have an item associated with it. =#
         @Uniontype Item begin
              @Record ITEM begin

                       key #= Key =#::Key
                       val #= Val =#::Val
              end

              @Record NO_ITEM begin

              end
         end

        import Error

         #= return the name of the tree =#
        function name(tree::Tree{<:Key, Val}) ::String 
              local name::String

              @match TREE(name = name) = tree
          name
        end

         #= Return an empty tree with the given printing functions attached =#
        function create(name::String #= a name for this tree so you know which one it is if you have more =#, inKeyCompareFunc::FuncTypeKeyCompare, inKeyStrFuncOpt::Option{<:FuncTypeKeyToStr}, inValStrFuncOpt::Option{<:FuncTypeValToStr}, inUpdateCheckFuncOpt::Option{<:FuncTypeItemUpdateCheck}) ::Tree{Key, Val} 
              local tree::Tree{Key, Val}

              tree = TREE(NODE(NO_ITEM(), 0, NO_NODE(), NO_NODE()), inKeyCompareFunc, inKeyStrFuncOpt, inValStrFuncOpt, inUpdateCheckFuncOpt, name)
          tree
        end

         #= returns true if you have set printing functions =#
        function hasPrintingFunctions(tree::Tree{<:Key, Val}) ::Bool 
              local hasPrinting::Bool

              local kf::Option{FuncTypeKeyToStr}
              local vf::Option{FuncTypeValToStr}

              @match TREE(keyStrFuncOpt = kf, valStrFuncOpt = vf) = tree
              hasPrinting = boolNot(boolOr(valueEq(NONE(), kf), valueEq(NONE(), vf)))
          hasPrinting
        end

         #= returns true if you have set printing functions =#
        function hasUpdateCheckFunction(tree::Tree{<:Key, Val}) ::Bool 
              local hasUpdateCheck::Bool

              local uf::Option{FuncTypeItemUpdateCheck}

              @match TREE(updateCheckFuncOpt = uf) = tree
              hasUpdateCheck = boolNot(valueEq(NONE(), uf))
          hasUpdateCheck
        end

         #= return the printing function pointer for the key, fails if you haven't set any =#
        function getUpdateCheckFunc(tree::Tree{<:Key, Val}) ::FuncTypeItemUpdateCheck 
              local outUpdateCheckFunc::FuncTypeItemUpdateCheck

              @match TREE(updateCheckFuncOpt = SOME(outUpdateCheckFunc)) = tree
          outUpdateCheckFunc
        end

         #= return the printing function pointer for the key, fails if you haven't set any =#
        function getKeyCompareFunc(tree::Tree{<:Key, Val}) ::FuncTypeKeyCompare 
              local outKeyCompareFunc::FuncTypeKeyCompare

              @match TREE(keyCompareFunc = outKeyCompareFunc) = tree
          outKeyCompareFunc
        end

         #= return the printing function pointer for the key, fails if you haven't set any =#
        function getKeyToStrFunc(tree::Tree{<:Key, Val}) ::FuncTypeKeyToStr 
              local outKey2StrFunc::FuncTypeKeyToStr

              @match TREE(keyStrFuncOpt = SOME(outKey2StrFunc)) = tree
          outKey2StrFunc
        end

         #= return the printing function pointer for the val, fails if you haven't set any =#
        function getValToStrFunc(tree::Tree{<:Key, Val}) ::FuncTypeValToStr 
              local outVal2StrFunc::FuncTypeValToStr

              @match TREE(valStrFuncOpt = SOME(outVal2StrFunc)) = tree
          outVal2StrFunc
        end

        function newLeafNode(inItem::Item{<:Key, Val}, height::ModelicaInteger) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = NODE(inItem, 1, NO_NODE(), NO_NODE())
          outNode
        end

         #= inserts a new item into the tree. =#
        function add(inTree::Tree{<:Key, Val}, inKey::Key, inVal::Val) ::Tree{Key, Val} 
              local outTree::Tree{Key, Val}

              outTree = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local node::Node{Key, Val}
                  local cf::FuncTypeKeyCompare
                  local kf::Option{FuncTypeKeyToStr}
                  local vf::Option{FuncTypeValToStr}
                  local uf::Option{FuncTypeItemUpdateCheck}
                  local str::String
                  local n::String
                   #=  call addNode on the root
                   =#
                @matchcontinue (inTree, inKey, inVal) begin
                  (TREE(node, cf, kf, vf, uf, n), key, val)  => begin
                      node = addNode(inTree, node, key, val)
                    TREE(node, cf, kf, vf, uf, n)
                  end
                  
                  _  => begin
                        str = "AvlTree.add name: " + name(inTree) + " failed!"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  send the tree down to the nodes for compare function and update check
               =#
          outTree
        end

         #= Inserts a new item into the tree root node =#
        function addNode(inTree::Tree{<:Key, Val} #= sent down so we can use the update check function =#, inNode::Node{<:Key, Val} #= the node to add item to =#, inKey::Key, inVal::Val) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local item::Item{Key, Val}
                  local keyCompareFunc::FuncTypeKeyCompare
                  local n::Node{Key, Val}
                  local order::ModelicaInteger
                  local str::String
                   #=  empty node
                   =#
                @match (inTree, inNode, inKey, inVal) begin
                  (_, NO_NODE(__), _, _)  => begin
                      n = newLeafNode(ITEM(inKey, inVal), 1)
                    n
                  end
                  
                  (_, NODE(item = NO_ITEM(__), left = NO_NODE(__), right = NO_NODE(__)), key, val)  => begin
                      n = newLeafNode(ITEM(key, val), 1)
                    n
                  end
                  
                  (TREE(keyCompareFunc = keyCompareFunc), NODE(item = ITEM(key = rkey)), key, val)  => begin
                      order = keyCompareFunc(key, rkey)
                      n = balance(addNode_dispatch(inTree, inNode, order, key, val))
                    n
                  end
                  
                  _  => begin
                        str = "AvlTree.addNode name: " + name(inTree) + " failed!"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  empty node item
               =#
          outNode
        end

         #= Helper function to addNode. =#
        function addNode_dispatch(inTree::Tree{<:Key, Val} #= sent down so we can use the update check function =#, inNode::Node{<:Key, Val}, inKeyComp::ModelicaInteger, inKey::Key, inVal::Val) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local key::Key
                  local val::Val
                  local l::Node{Key, Val}
                  local r::Node{Key, Val}
                  local n::Node{Key, Val}
                  local h::ModelicaInteger
                  local i::Item{Key, Val}
                  local updateCheckFunc::FuncTypeItemUpdateCheck
                   #=  replacements of nodes is allowed! no update check function
                   =#
                @matchcontinue (inTree, inNode, inKeyComp, inKey, inVal) begin
                  (_, NODE(_, h, l, r), 0, key, val)  => begin
                      @match false = hasUpdateCheckFunction(inTree)
                    NODE(ITEM(key, val), h, l, r)
                  end
                  
                  (_, NODE(i, h, l, r), 0, key, val)  => begin
                      @match true = hasUpdateCheckFunction(inTree)
                      updateCheckFunc = getUpdateCheckFunc(inTree)
                      @match true = updateCheckFunc(i, ITEM(key, val))
                    NODE(ITEM(key, val), h, l, r)
                  end
                  
                  (_, NODE(i, _, _, _), 0, key, val)  => begin
                      @match true = hasUpdateCheckFunction(inTree)
                      updateCheckFunc = getUpdateCheckFunc(inTree)
                      @match false = updateCheckFunc(i, ITEM(key, val))
                    inNode
                  end
                  
                  (_, NODE(item = i, height = h, left = l, right = r), 1, key, val)  => begin
                      n = emptyNodeIfNoNode(r)
                      n = addNode(inTree, n, key, val)
                    NODE(i, h, l, n)
                  end
                  
                  (_, NODE(item = i, height = h, left = l, right = r), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key, val)  => begin
                      n = emptyNodeIfNoNode(l)
                      n = addNode(inTree, n, key, val)
                    NODE(i, h, n, r)
                  end
                end
              end
               #=  replacements of nodes maybe allowed!
               =#
               #=  we have an update check function
               =#
               #=  update is allowed
               =#
               #=  replacements of nodes maybe allowed!
               =#
               #=  we have an update check function
               =#
               #=  update is NOT allowed
               =#
               #=  return the same node, no update!
               =#
               #=  insert into right subtree.
               =#
               #=  Insert into left subtree.
               =#
          outNode
        end

         #= Get a Val from the binary tree given a key. =#
        function get(inTree::Tree{<:Key, Val}, inKey::Key) ::Val 
              local outVal::Val

              local node::Node{Key, Val}

              @match TREE(root = node) = inTree
              outVal = getNode(inTree, node, inKey)
               #=  send the tree down for the compare func!
               =#
          outVal
        end

         #= Get a Val from the binary tree node given a key. =#
        function getNode(inTree::Tree{<:Key, Val}, inNode::Node{<:Key, Val}, inKey::Key) ::Val 
              local outVal::Val

              local rkey::Key
              local keyCompareFunc::FuncTypeKeyCompare
              local order::ModelicaInteger

              @match NODE(item = ITEM(key = rkey)) = inNode
              keyCompareFunc = getKeyCompareFunc(inTree)
              order = keyCompareFunc(inKey, rkey)
              outVal = getNode_dispatch(inTree, inNode, order, inKey)
          outVal
        end

         #= Helper function to getNode. =#
        function getNode_dispatch(inTree::Tree{<:Key, Val}, inNode::Node{<:Key, Val}, inKeyComp::ModelicaInteger, inKey::Key) ::Val 
              local outVal::Val

              outVal = begin
                  local key::Key
                  local val::Val
                  local l::Node{Key, Val}
                  local r::Node{Key, Val}
                   #=  found match.
                   =#
                @match (inTree, inNode, inKeyComp, inKey) begin
                  (_, NODE(item = ITEM(val = val)), 0, _)  => begin
                    val
                  end
                  
                  (_, NODE(right = r), 1, key)  => begin
                    getNode(inTree, r, key)
                  end
                  
                  (_, NODE(left = l), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key)  => begin
                    getNode(inTree, l, key)
                  end
                end
              end
               #=  search to the right.
               =#
               #=  search to the left.
               =#
          outVal
        end

         #= Replaces the item of an already existing node in the tree with a new item.
         Note that the update check function is not used if replace is called! =#
        function replace(inTree::Tree{<:Key, Val}, inKey::Key, inVal::Val) ::Tree{Key, Val} 
              local outTree::Tree{Key, Val}

              outTree = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local keyCompareFunc::FuncTypeKeyCompare
                  local kf::Option{FuncTypeKeyToStr}
                  local vf::Option{FuncTypeValToStr}
                  local uf::Option{FuncTypeItemUpdateCheck}
                  local node::Node{Key, Val}
                  local order::ModelicaInteger
                  local n::String
                  local str::String
                @match (inTree, inKey, inVal) begin
                  (TREE(node, keyCompareFunc, kf, vf, uf, n), key, val)  => begin
                      node = replaceNode(inTree, node, key, val)
                    TREE(node, keyCompareFunc, kf, vf, uf, n)
                  end
                  
                  _  => begin
                        str = "AvlTree.replace name: " + name(inTree) + " failed!"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
          outTree
        end

         #= Replaces the item of an already existing node in the tree with a new value. =#
        function replaceNode(inTree::Tree{<:Key, Val} #= send down for comparison function =#, inNode::Node{<:Key, Val}, inKey::Key, inVal::Val) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local keyCompareFunc::FuncTypeKeyCompare
                  local n::Node{Key, Val}
                  local order::ModelicaInteger
                @match (inTree, inNode, inKey, inVal) begin
                  (TREE(keyCompareFunc = keyCompareFunc), NODE(item = ITEM(key = rkey)), key, val)  => begin
                      order = keyCompareFunc(key, rkey)
                      n = replaceNode_dispatch(inTree, inNode, order, key, val)
                    n
                  end
                end
              end
          outNode
        end

         #= Helper function to replaceNode. =#
        function replaceNode_dispatch(inTree::Tree{<:Key, Val} #= send down for comparison function =#, inNode::Node{<:Key, Val}, inKeyComp::ModelicaInteger, inKey::Key, inVal::Val) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local l::Node{Key, Val}
                  local r::Node{Key, Val}
                  local n::Node{Key, Val}
                  local h::ModelicaInteger
                  local i::Item{Key, Val}
                   #=  replace this node.
                   =#
                @match (inTree, inNode, inKeyComp, inKey, inVal) begin
                  (_, NODE(item = ITEM(__), height = h, left = l, right = r), 0, key, val)  => begin
                    NODE(ITEM(key, val), h, l, r)
                  end
                  
                  (_, NODE(item = i, height = h, left = l, right = r), 1, key, val)  => begin
                      n = emptyNodeIfNoNode(r)
                      n = replaceNode(inTree, n, key, val)
                    NODE(i, h, l, n)
                  end
                  
                  (_, NODE(item = i, height = h, left = l, right = r), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key, val)  => begin
                      n = emptyNodeIfNoNode(l)
                      n = replaceNode(inTree, n, key, val)
                    NODE(i, h, n, r)
                  end
                end
              end
               #=  insert into right subtree.
               =#
               #=  insert into left subtree.
               =#
          outNode
        end

         #= creates an empty node if the node is NO_NODE =#
        function emptyNodeIfNoNode(inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                @match inNode begin
                  NO_NODE(__)  => begin
                    NODE(NO_ITEM(), 0, NO_NODE(), NO_NODE())
                  end
                  
                  NODE(__)  => begin
                    inNode
                  end
                end
              end
          outNode
        end

         #= Balances an Node<Key,Val> =#
        function balance(inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              local d::ModelicaInteger

              d = differenceInHeight(inNode)
              outNode = doBalance(d, inNode)
          outNode
        end

         #= Performs balance if difference is > 1 or < -1 =#
        function doBalance(difference::ModelicaInteger, inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                @match (difference, inNode) begin
                  (#= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, _)  => begin
                    computeHeight(inNode)
                  end
                  
                  (0, _)  => begin
                    computeHeight(inNode)
                  end
                  
                  (1, _)  => begin
                    computeHeight(inNode)
                  end
                  
                  _  => begin
                      doBalance2(difference < 0, inNode)
                  end
                end
              end
               #=  d < -1 or d > 1
               =#
          outNode
        end

         #= Help function to doBalance =#
        function doBalance2(inDiffIsNegative::Bool, inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local n::Node{Key, Val}
                @match (inDiffIsNegative, inNode) begin
                  (true, n)  => begin
                      n = doBalance3(n)
                      n = rotateLeft(n)
                    n
                  end
                  
                  (false, n)  => begin
                      n = doBalance4(n)
                      n = rotateRight(n)
                    n
                  end
                end
              end
          outNode
        end

         #= help function to doBalance2 =#
        function doBalance3(inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local n::Node{Key, Val}
                  local rr::Node{Key, Val}
                  local rN::Node{Key, Val}
                @matchcontinue inNode begin
                  n  => begin
                      rN = rightNode(n)
                      @match true = differenceInHeight(rN) > 0
                      rr = rotateRight(rN)
                      n = setRight(n, rr)
                    n
                  end
                  
                  _  => begin
                      inNode
                  end
                end
              end
          outNode
        end

         #= Help function to doBalance2 =#
        function doBalance4(inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              outNode = begin
                  local rl::Node{Key, Val}
                  local n::Node{Key, Val}
                  local lN::Node{Key, Val}
                @matchcontinue inNode begin
                  n  => begin
                      lN = leftNode(n)
                      @match true = differenceInHeight(lN) < 0
                      rl = rotateLeft(lN)
                      n = setLeft(n, rl)
                    n
                  end
                  
                  _  => begin
                      inNode
                  end
                end
              end
          outNode
        end

         #= set right treenode =#
        function setRight(node::Node{<:Key, Val}, right::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              local item::Item{Key, Val}
              local l::Node{Key, Val}
              local height::ModelicaInteger

              @match NODE(item, height, l, _) = node
              outNode = NODE(item, height, l, right)
          outNode
        end

         #= set left node =#
        function setLeft(node::Node{<:Key, Val}, left::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              local item::Item{Key, Val}
              local r::Node{Key, Val}
              local height::ModelicaInteger

              @match NODE(item, height, _, r) = node
              outNode = NODE(item, height, left, r)
          outNode
        end

         #= Retrieve the left subnode =#
        function leftNode(node::Node{<:Key, Val}) ::Node{Key, Val} 
              local subNode::Node{Key, Val}

              @match NODE(left = subNode) = node
          subNode
        end

         #= Retrieve the right subnode =#
        function rightNode(node::Node{<:Key, Val}) ::Node{Key, Val} 
              local subNode::Node{Key, Val}

              @match NODE(right = subNode) = node
          subNode
        end

         #= help function to balance =#
        function exchangeLeft(inNode::Node{<:Key, Val}, inParent::Node{<:Key, Val}) ::Node{Key, Val} 
              local outParent::Node{Key, Val} #= updated parent =#

              local parent::Node{Key, Val}
              local node::Node{Key, Val}

              parent = setRight(inParent, leftNode(inNode))
              parent = balance(parent)
              node = setLeft(inNode, parent)
              outParent = balance(node)
          outParent #= updated parent =#
        end

         #= help function to balance =#
        function exchangeRight(inNode::Node{<:Key, Val}, inParent::Node{<:Key, Val}) ::Node{Key, Val} 
              local outParent::Node{Key, Val} #= updated parent =#

              local parent::Node{Key, Val}
              local node::Node{Key, Val}

              parent = setLeft(inParent, rightNode(inNode))
              parent = balance(parent)
              node = setRight(inNode, parent)
              outParent = balance(node)
          outParent #= updated parent =#
        end

         #= help function to balance =#
        function rotateLeft(node::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val} #= updated node =#

              outNode = exchangeLeft(rightNode(node), node)
          outNode #= updated node =#
        end

         #= help function to balance =#
        function rotateRight(node::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val} #= updated node =#

              outNode = exchangeRight(leftNode(node), node)
          outNode #= updated node =#
        end

         #= help function to balance, calculates the difference in height between left
          and right child =#
        function differenceInHeight(node::Node{<:Key, Val}) ::ModelicaInteger 
              local diff::ModelicaInteger

              local l::Node{Key, Val}
              local r::Node{Key, Val}

              @match NODE(left = l, right = r) = node
              diff = getHeight(l) - getHeight(r)
          diff
        end

         #= compute the heigth of the Tree and store in the node info =#
        function computeHeight(inNode::Node{<:Key, Val}) ::Node{Key, Val} 
              local outNode::Node{Key, Val}

              local l::Node{Key, Val}
              local r::Node{Key, Val}
              local i::Item{Key, Val}
              local val::Val
              local hl::ModelicaInteger
              local hr::ModelicaInteger
              local height::ModelicaInteger

              @match NODE(item = (@match ITEM() = i), left = l, right = r) = inNode
              hl = getHeight(l)
              hr = getHeight(r)
              height = intMax(hl, hr) + 1
              outNode = NODE(i, height, l, r)
          outNode
        end

         #= Retrieve the height of a node =#
        function getHeight(bt::Node{<:Key, Val}) ::ModelicaInteger 
              local height::ModelicaInteger

              height = begin
                @match bt begin
                  NO_NODE(__)  => begin
                    0
                  end
                  
                  NODE(height = height)  => begin
                    height
                  end
                end
              end
          height
        end

        function prettyPrintTreeStr(inTree::Tree{<:Key, Val}) ::String 
              local outString::String

              outString = prettyPrintTreeStr_dispatch(inTree, "")
          outString
        end

        function prettyPrintTreeStr_dispatch(inTree::Tree{<:Key, Val}, inIndent::String) ::String 
              local outString::String

              local node::Node{Key, Val}

              if ! hasPrintingFunctions(inTree)
                outString = "TreePrintError<NO_PRINTING_FUNCTIONS_ATTACHED> name[" + name(inTree) + "]"
                return outString
              end
              @match TREE(root = node) = inTree
              outString = prettyPrintNodeStr(inTree, node, inIndent)
          outString
        end

        function prettyPrintNodeStr(inTree::Tree{<:Key, Val}, inNode::Node{<:Key, Val}, inIndent::String) ::String 
              local outString::String

              outString = begin
                  local item::Item{Key, Val}
                  local node::Node{Key, Val}
                  local l::Node{Key, Val}
                  local r::Node{Key, Val}
                  local keyStrFunc::FuncTypeKeyToStr
                  local valStrFunc::FuncTypeValToStr
                  local indent::String
                  local s1::String
                  local s2::String
                  local res::String
                @match (inTree, inNode, inIndent) begin
                  (_, NO_NODE(__), _)  => begin
                    ""
                  end
                  
                  (_, NODE(item = NO_ITEM(__), left = l, right = r), _)  => begin
                      indent = inIndent + "  "
                      s1 = prettyPrintNodeStr(inTree, l, indent)
                      s2 = prettyPrintNodeStr(inTree, r, indent)
                      res = "\\n" + s1 + s2
                    res
                  end
                  
                  (_, NODE(item = item && ITEM(__), left = l, right = r), _)  => begin
                      indent = inIndent + "  "
                      s1 = prettyPrintNodeStr(inTree, l, indent)
                      s2 = prettyPrintNodeStr(inTree, r, indent)
                      res = "\\n" + inIndent + printItemStr(inTree, item) + s1 + s2
                    res
                  end
                end
              end
          outString
        end

        function printTreeStr(inTree::Tree{<:Key, Val}) ::String 
              local outString::String

              local node::Node{Key, Val}

              if ! hasPrintingFunctions(inTree)
                outString = "TreePrintError<NO_PRINTING_FUNCTIONS_ATTACHED> name[" + name(inTree) + "]"
                return outString
              end
              @match TREE(root = node) = inTree
              outString = printNodeStr(inTree, node)
          outString
        end

        function printNodeStr(inTree::Tree{<:Key, Val}, inNode::Node{<:Key, Val}) ::String 
              local outString::String

              outString = begin
                  local left::Node{Key, Val}
                  local right::Node{Key, Val}
                  local item::Item{Key, Val}
                  local left_str::String
                  local right_str::String
                  local item_str::String
                  local str::String
                @match (inTree, inNode) begin
                  (_, NO_NODE(__))  => begin
                    ""
                  end
                  
                  (_, NODE(item = NO_ITEM(__)))  => begin
                    ""
                  end
                  
                  (_, NODE(item = item && ITEM(__), left = left, right = right))  => begin
                      left_str = printNodeStr(inTree, left)
                      right_str = printNodeStr(inTree, right)
                      item_str = printItemStr(inTree, item)
                      str = stringAppendList(list("i: ", item_str, ", l: ", left_str, ", r: ", right_str))
                    str
                  end
                end
              end
          outString
        end

        function printItemStr(inTree::Tree{<:Key, Val}, inItem::Item{<:Key, Val}) ::String 
              local outString::String

              outString = begin
                  local str::String
                  local keyStr::String
                  local valStr::String
                  local key2Str::FuncTypeKeyToStr
                  local val2Str::FuncTypeValToStr
                  local key::Key
                  local val::Val
                @match (inTree, inItem) begin
                  (_, NO_ITEM(__))  => begin
                    "[]"
                  end
                  
                  (_, ITEM(key = key, val = val))  => begin
                      key2Str = getKeyToStrFunc(inTree)
                      val2Str = getValToStrFunc(inTree)
                      keyStr = key2Str(key)
                      valStr = val2Str(val)
                      str = "[" + keyStr + ", " + valStr + "]"
                    str
                  end
                end
              end
          outString
        end

         #= search for a key that has val as value, fails if it cannot find it;
         if there are multiple keys pointing to the same value only the first
         one encountered is returned =#
        function getKeyOfVal(inTree::Tree{<:Key, Val}, inVal::Val) ::Key 
              local outKey::Key

              local node::Node{Key, Val}
              local key::Key

              @match TREE(root = node) = inTree
              outKey = getKeyOfValNode(inTree, node, inVal)
          outKey
        end

        function getKeyOfValNode(inTree::Tree{<:Key, Val}, inNode::Node{<:Key, Val}, inVal::Val) ::Key 
              local outKey::Key

              outKey = begin
                  local left::Node{Key, Val}
                  local right::Node{Key, Val}
                  local item::Item{Key, Val}
                  local v::Val
                  local k::Key
                @matchcontinue inNode begin
                  NODE(item = ITEM(k, v))  => begin
                      @match true = valueEq(v, inVal)
                    k
                  end
                  
                  NODE(item = ITEM(_, v), left = left)  => begin
                      @match false = valueEq(v, inVal)
                      k = getKeyOfValNode(inTree, left, inVal)
                    k
                  end
                  
                  NODE(item = ITEM(_, v), right = right)  => begin
                      @match false = valueEq(v, inVal)
                      k = getKeyOfValNode(inTree, right, inVal)
                    k
                  end
                end
              end
               #=  search left
               =#
               #=  search right
               =#
          outKey
        end

         #= inserts a new item into the tree if is not there
         and returns the new item.
         if the key is there then it returns the already
         exiting item and doe not update the tree. =#
        function addUnique(inTree::Tree{<:Key, Val}, inKey::Key, inVal::Val) ::Tuple{Tree{Key, Val}, Item{Key, Val}} 
              local outItem::Item{Key, Val}
              local outTree::Tree{Key, Val}

              (outTree, outItem) = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local node::Node{Key, Val}
                  local cf::FuncTypeKeyCompare
                  local kf::Option{FuncTypeKeyToStr}
                  local vf::Option{FuncTypeValToStr}
                  local uf::Option{FuncTypeItemUpdateCheck}
                  local str::String
                  local n::String
                  local item::Item{Key, Val}
                   #=  call addNode on the root
                   =#
                @matchcontinue (inTree, inKey, inVal) begin
                  (TREE(node, cf, kf, vf, uf, n), key, val)  => begin
                      (node, item) = addNodeUnique(inTree, node, key, val)
                    (TREE(node, cf, kf, vf, uf, n), item)
                  end
                  
                  _  => begin
                        str = "AvlTree.addUnique name: " + name(inTree) + " failed!"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  send the tree down to the nodes for compare function and update check
               =#
          (outTree, outItem)
        end

         #= Inserts a new item into the tree root node if is not there and returns the new item.
         if is there it returns the existing item. =#
        function addNodeUnique(inTree::Tree{<:Key, Val} #= sent down so we can use the update check function =#, inNode::Node{<:Key, Val} #= the node to add item to =#, inKey::Key, inVal::Val) ::Tuple{Node{Key, Val}, Item{Key, Val}} 
              local outItem::Item{Key, Val}
              local outNode::Node{Key, Val}

              (outNode, outItem) = begin
                  local key::Key
                  local rkey::Key
                  local val::Val
                  local item::Item{Key, Val}
                  local keyCompareFunc::FuncTypeKeyCompare
                  local n::Node{Key, Val}
                  local order::ModelicaInteger
                  local str::String
                   #=  empty node
                   =#
                @match (inTree, inNode, inKey, inVal) begin
                  (_, NO_NODE(__), _, _)  => begin
                      item = ITEM(inKey, inVal)
                      n = newLeafNode(item, 1)
                    (n, item)
                  end
                  
                  (_, NODE(item = NO_ITEM(__), left = NO_NODE(__), right = NO_NODE(__)), key, val)  => begin
                      item = ITEM(key, val)
                      n = newLeafNode(item, 1)
                    (n, item)
                  end
                  
                  (TREE(keyCompareFunc = keyCompareFunc), NODE(item = ITEM(key = rkey)), key, val)  => begin
                      order = keyCompareFunc(key, rkey)
                      (n, item) = addNodeUnique_dispatch(inTree, inNode, order, key, val)
                      n = balance(n)
                    (n, item)
                  end
                  
                  _  => begin
                        str = "AvlTree.addNodeUnique name: " + name(inTree) + " failed!"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  empty node item
               =#
          (outNode, outItem)
        end

         #= Helper function to addNode. =#
        function addNodeUnique_dispatch(inTree::Tree{<:Key, Val} #= sent down so we can use the update check function =#, inNode::Node{<:Key, Val}, inKeyComp::ModelicaInteger, inKey::Key, inVal::Val) ::Tuple{Node{Key, Val}, Item{Key, Val}} 
              local outItem::Item{Key, Val}
              local outNode::Node{Key, Val}

              (outNode, outItem) = begin
                  local key::Key
                  local val::Val
                  local l::Node{Key, Val}
                  local r::Node{Key, Val}
                  local n::Node{Key, Val}
                  local h::ModelicaInteger
                  local i::Item{Key, Val}
                  local it::Item{Key, Val}
                  local updateCheckFunc::FuncTypeItemUpdateCheck
                   #=  replacements of nodes are not allowed in addUnique
                   =#
                   #=  we don't care about update check functions here
                   =#
                @match (inTree, inNode, inKeyComp, inKey, inVal) begin
                  (_, NODE(i, _, _, _), 0, _, _)  => begin
                    (inNode, i)
                  end
                  
                  (_, NODE(item = i, height = h, left = l, right = r), 1, key, val)  => begin
                      n = emptyNodeIfNoNode(r)
                      (n, it) = addNodeUnique(inTree, n, key, val)
                    (NODE(i, h, l, n), it)
                  end
                  
                  (_, NODE(item = i, height = h, left = l, right = r), #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#, key, val)  => begin
                      n = emptyNodeIfNoNode(l)
                      (n, it) = addNodeUnique(inTree, n, key, val)
                    (NODE(i, h, n, r), it)
                  end
                end
              end
               #=  return the same node, no update for addUnique!
               =#
               #=  insert into right subtree.
               =#
               #=  Insert into left subtree.
               =#
          (outNode, outItem)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end