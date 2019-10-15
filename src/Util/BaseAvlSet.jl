  #=TODO: Originally partial =# module BaseAvlSet


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Tree
    keyStr = Function
    keyCompare = Function

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
        const Key = Any
        const Value = Any

          #= The binary tree data structure. =#
         @Uniontype Tree begin
              @Record NODE begin

                       key #= The key of the node. =#::Key
                       value::Value
                       height #= Height of tree, used for balancing =#::ModelicaInteger
                       left #= Left subtree. =#::Tree
                       right #= Right subtree. =#::Tree
              end

              @Record LEAF begin

                       key #= The key of the node. =#::Key
                       value::Value
              end

              @Record EMPTY begin

              end
         end

        const ValueNode = Key

        function printNodeStr(inNode::Tree) ::String
              local outString::String

              outString = begin
                @match inNode begin
                  NODE(__)  => begin
                    keyStr(inNode.key)
                  end

                  LEAF(__)  => begin
                    keyStr(inNode.key)
                  end
                end
              end
          outString
        end

         #= Return an empty tree =#
        function new() ::Tree
              local outTree::Tree = EMPTY()
          outTree
        end

         #= Inserts a new node in the tree. =#
        function add(inTree::Tree, inKey::Key) ::Tree
              local tree::Tree = inTree

              tree = begin
                  local key::Key
                  local key_comp::ModelicaInteger
                  local outTree::Tree
                   #=  Empty tree.
                   =#
                @match tree begin
                  EMPTY(__)  => begin
                    LEAF(inKey)
                  end

                  NODE(key = key)  => begin
                      key_comp = keyCompare(inKey, key)
                      if key_comp == (-1)
                        tree.left = add(tree.left, inKey)
                      elseif key_comp == 1
                        tree.right = add(tree.right, inKey)
                      end
                       #=  Replace left branch.
                       =#
                       #=  Replace right branch.
                       =#
                    if key_comp == 0
                          tree
                        else
                          balance(tree)
                        end
                  end

                  LEAF(key = key)  => begin
                      key_comp = keyCompare(inKey, key)
                      if key_comp == (-1)
                        outTree = NODE(tree.key, 2, LEAF(inKey), EMPTY())
                      elseif key_comp == 1
                        outTree = NODE(tree.key, 2, EMPTY(), LEAF(inKey))
                      else
                        outTree = tree
                      end
                       #=  Replace left branch.
                       =#
                       #=  Replace right branch.
                       =#
                    outTree
                  end
                end
              end
               #=  No need to balance addition in a leaf
               =#
          tree
        end

         #= Adds a list of key-value pairs to the tree. =#
        function addList(tree::Tree, inValues::List{<:Key}) ::Tree


              for key in inValues
                tree = add(tree, key)
              end
          tree
        end

         #= Gets a value from the tree given a key. =#
        function hasKey(inTree::Tree, inKey::Key) ::Bool
              local comp::Bool = false

              local key::Key
              local key_comp::ModelicaInteger
              local tree::Tree

              key = begin
                @match inTree begin
                  NODE(__)  => begin
                    inTree.key
                  end

                  LEAF(__)  => begin
                    inTree.key
                  end

                  EMPTY(__)  => begin
                      return
                    fail()
                  end
                end
              end
              key_comp = keyCompare(inKey, key)
              comp = begin
                @match (key_comp, inTree) begin
                  (0, _)  => begin
                    true
                  end

                  (1, NODE(right = tree))  => begin
                    hasKey(tree, inKey)
                  end

                  (-1, NODE(left = tree))  => begin
                    hasKey(tree, inKey)
                  end

                  _  => begin
                      false
                  end
                end
              end
          comp
        end

        function isEmpty(tree::Tree) ::Bool
              local isEmpty::Bool

              isEmpty = begin
                @match tree begin
                  EMPTY(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isEmpty
        end

         #= Converts the tree to a flat list of keys (in order). =#
        function listKeys(inTree::Tree, lst::List{<:Key} = nil) ::List{Key}


              lst = begin
                @match inTree begin
                  LEAF(__)  => begin
                    _cons(inTree.key, lst)
                  end

                  NODE(__)  => begin
                      lst = listKeys(inTree.right, lst)
                      lst = _cons(inTree.key, lst)
                      lst = listKeys(inTree.left, lst)
                    lst
                  end

                  _  => begin
                      lst
                  end
                end
              end
          lst
        end

         #= Converts the tree to a flat list of keys (in order). =#
        function listKeysReverse(inTree::Tree, lst::List{<:Key} = nil) ::List{Key}


              lst = begin
                @match inTree begin
                  LEAF(__)  => begin
                    _cons(inTree.key, lst)
                  end

                  NODE(__)  => begin
                      lst = listKeysReverse(inTree.left, lst)
                      lst = _cons(inTree.key, lst)
                      lst = listKeysReverse(inTree.right, lst)
                    lst
                  end

                  _  => begin
                      lst
                  end
                end
              end
          lst
        end

         #= Joins two trees by adding the second one to the first. =#
        function join(tree::Tree, treeToJoin::Tree) ::Tree


              tree = begin
                @match treeToJoin begin
                  EMPTY(__)  => begin
                    tree
                  end

                  NODE(__)  => begin
                      tree = add(tree, treeToJoin.key)
                      tree = join(tree, treeToJoin.left)
                      tree = join(tree, treeToJoin.right)
                    tree
                  end

                  LEAF(__)  => begin
                    add(tree, treeToJoin.key)
                  end
                end
              end
          tree
        end

         #= Prints the tree to a string using UTF-8 box-drawing characters to construct a
           graphical view of the tree. =#
        function printTreeStr(inTree::Tree) ::String
              local outString::String

              local left::Tree
              local right::Tree

              outString = begin
                @match inTree begin
                  EMPTY(__)  => begin
                    "EMPTY()"
                  end

                  LEAF(__)  => begin
                    printNodeStr(inTree)
                  end

                  NODE(left = left, right = right)  => begin
                    printTreeStr2(left, true, "") + printNodeStr(inTree) + "\\n" + printTreeStr2(right, false, "")
                  end
                end
              end
          outString
        end

        function setTreeLeftRight(orig::Tree, left::Tree = EMPTY(), right::Tree = EMPTY()) ::Tree
              local res::Tree

              res = begin
                @match (orig, left, right) begin
                  (NODE(__), EMPTY(__), EMPTY(__))  => begin
                    LEAF(orig.key)
                  end

                  (LEAF(__), EMPTY(__), EMPTY(__))  => begin
                    orig
                  end

                  (NODE(__), _, _)  => begin
                    if referenceEqOrEmpty(orig.left, left) && referenceEqOrEmpty(orig.right, right)
                          orig
                        else
                          NODE(orig.key, max(height(left), height(right)) + 1, left, right)
                        end
                  end

                  (LEAF(__), _, _)  => begin
                    NODE(orig.key, max(height(left), height(right)) + 1, left, right)
                  end
                end
              end
          res
        end

         #= Takes two sets and returns the intersection as well as the remainder
          of both sets after removing the duplicates in both sets. =#
        function intersection(tree1::Tree, tree2::Tree) ::Tree
              local intersect::Tree = Tree.EMPTY()
              local rest1::Tree = Tree.EMPTY()
              local rest2::Tree = Tree.EMPTY()

              local keylist1::List{Key}
              local keylist2::List{Key}
              local k1::Key
              local k2::Key
              local key_comp::ModelicaInteger

              if isEmpty(tree1)
                rest2 = tree2
                return intersect, rest1, rest2
              end
              if isEmpty(tree2)
                rest1 = tree1
                return intersect, rest1, rest2
              end
               #=  we operate on sorted lists from the trees!
               =#
              @match _cons(k1, keylist1) = listKeys(tree1)
              @match _cons(k2, keylist2) = listKeys(tree2)
              while true
                key_comp = keyCompare(k1, k2)
                if key_comp > 0
                  if isPresent(rest2)
                    rest2 = add(rest2, k2)
                  end
                  if listEmpty(keylist2)
                    break
                  end
                  @match _cons(k2, keylist2) = keylist2
                elseif key_comp < 0
                  if isPresent(rest1)
                    rest1 = add(rest1, k1)
                  end
                  if listEmpty(keylist1)
                    break
                  end
                  @match _cons(k1, keylist1) = keylist1
                else
                  intersect = add(intersect, k1)
                  if listEmpty(keylist1) || listEmpty(keylist2)
                    break
                  end
                  @match _cons(k1, keylist1) = keylist1
                  @match _cons(k2, keylist2) = keylist2
                end
              end
               #=  equal keys: advance both lists
               =#
              if isPresent(rest1) && ! listEmpty(keylist1)
                for key in keylist1
                  rest1 = add(rest1, key)
                end
              end
              if isPresent(rest2) && ! listEmpty(keylist2)
                for key in keylist2
                  rest2 = add(rest2, key)
                end
              end
          intersect, rest1, rest2
        end

        function referenceEqOrEmpty(t1::Tree, t2::Tree) ::Bool
              local b::Bool

              b = begin
                @match (t1, t2) begin
                  (EMPTY(__), EMPTY(__))  => begin
                    true
                  end

                  _  => begin
                      referenceEq(t1, t2)
                  end
                end
              end
          b
        end

         #= Balances a Tree =#
        function balance(inTree)
              local outTree::Tree = inTree

              outTree = begin
                  local lh::ModelicaInteger
                  local rh::ModelicaInteger
                  local diff::ModelicaInteger
                  local child::Tree
                  local balanced_tree::Tree
                @match outTree begin
                  LEAF(__)  => begin
                    inTree
                  end

                  NODE(__)  => begin
                      lh = height(outTree.left)
                      rh = height(outTree.right)
                      diff = lh - rh
                      if diff < (-1)
                        balanced_tree = if calculateBalance(outTree.right) > 0
                              rotateLeft(setTreeLeftRight(outTree, left = outTree.left, right = rotateRight(outTree.right)))
                            else
                              rotateLeft(outTree)
                            end
                      elseif diff > 1
                        balanced_tree = if calculateBalance(outTree.left) < 0
                              rotateRight(setTreeLeftRight(outTree, left = rotateLeft(outTree.left), right = outTree.right))
                            else
                              rotateRight(outTree)
                            end
                      elseif outTree.height != max(lh, rh) + 1
                        outTree.height = max(lh, rh) + 1
                        balanced_tree = outTree
                      else
                        balanced_tree = outTree
                      end
                    balanced_tree
                  end
                end
              end
          outTree
        end

        function height(inNode::Tree) ::ModelicaInteger
              local outHeight::ModelicaInteger

              outHeight = begin
                @match inNode begin
                  NODE(__)  => begin
                    inNode.height
                  end

                  LEAF(__)  => begin
                    1
                  end

                  _  => begin
                      0
                  end
                end
              end
          outHeight
        end

        function calculateBalance(inNode::Tree) ::ModelicaInteger
              local outBalance::ModelicaInteger

              outBalance = begin
                @match inNode begin
                  NODE(__)  => begin
                    height(inNode.left) - height(inNode.right)
                  end

                  LEAF(__)  => begin
                    0
                  end

                  _  => begin
                      0
                  end
                end
              end
          outBalance
        end

         #= Performs an AVL left rotation on the given tree. =#
        function rotateLeft(inNode::Tree) ::Tree
              local outNode::Tree = inNode

              outNode = begin
                  local node::Tree
                  local child::Tree
                @match outNode begin
                  NODE(right = child && NODE(__))  => begin
                      node = setTreeLeftRight(outNode, left = outNode.left, right = child.left)
                    setTreeLeftRight(child, left = node, right = child.right)
                  end

                  NODE(right = child && LEAF(__))  => begin
                      node = setTreeLeftRight(outNode, left = outNode.left, right = EMPTY())
                    setTreeLeftRight(child, left = node, right = EMPTY())
                  end

                  _  => begin
                      inNode
                  end
                end
              end
          outNode
        end

         #= Performs an AVL right rotation on the given tree. =#
        function rotateRight(inNode::Tree) ::Tree
              local outNode::Tree = inNode

              outNode = begin
                  local node::Tree
                  local child::Tree
                @match outNode begin
                  NODE(left = child && NODE(__))  => begin
                      node = setTreeLeftRight(outNode, left = child.right, right = outNode.right)
                    setTreeLeftRight(child, right = node, left = child.left)
                  end

                  NODE(left = child && LEAF(__))  => begin
                      node = setTreeLeftRight(outNode, left = EMPTY(), right = outNode.right)
                    setTreeLeftRight(child, right = node, left = EMPTY())
                  end

                  _  => begin
                      inNode
                  end
                end
              end
          outNode
        end

         #= Helper function to printTreeStr. =#
        function printTreeStr2(inTree::Tree, isLeft::Bool, inIndent::String) ::String
              local outString::String

              local val_node::Option{ValueNode}
              local left::Option{Tree}
              local right::Option{Tree}
              local left_str::String
              local right_str::String

              outString = begin
                @match inTree begin
                  NODE(__)  => begin
                    printTreeStr2(inTree.left, true, inIndent + (if isLeft
                          "     "
                        else
                          " │   "
                        end)) + inIndent + (if isLeft
                          " ┌"
                        else
                          " └"
                        end) + "────" + printNodeStr(inTree) + "\\n" + printTreeStr2(inTree.right, false, inIndent + (if isLeft
                          " │   "
                        else
                          "     "
                        end))
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
