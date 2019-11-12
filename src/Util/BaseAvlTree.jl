
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

module BaseAvlTree

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

using Setfield

valueStr = Function
ConflictFunc = Function
EachFunc = Function
MapFunc = Function
FoldFunc = Function
MapFunc = Function

function keyStr end
function keyCompare end

import BaseAvlSet

const Key = Any
const Value = Any

Tree = BaseAvlSet.Tree
EMPTY = BaseAvlSet.EMPTY
NODE = BaseAvlSet.NODE
LEAF = BaseAvlSet.LEAF

function printNodeStr(inNode::Tree) ::String
    local outString::String

    outString = begin
        @match inNode begin
            NODE(__)  => begin
                "(" + keyStr(inNode.key) + ", " + valueStr(inNode.value) + ")"
            end

            LEAF(__)  => begin
                "(" + keyStr(inNode.key) + ", " + valueStr(inNode.value) + ")"
            end
        end
    end
    outString
end


#= Conflict resolving function for add which fails on conflict. =#
function addConflictFail(newValue::Value, oldValue::Value, key::Key) ::Value
    fail()
end


#= Default conflict resolving function for add. =#
addConflictDefault = addConflictFail

#= Conflict resolving function for add which replaces the old value with the new. =#
function addConflictReplace(newValue::Value, oldValue::Value, key::Key) ::Value
    local value::Value = newValue
    value
end

#= Conflict resolving function for add which keeps the old value. =#
function addConflictKeep(newValue::Value, oldValue::Value, key::Key) ::Value
    local value::Value = oldValue
    value
end


balance = BaseAvlSet.balance

#= Inserts a new node in the tree. =#
function add(inTree::Tree, inKey::Key, inValue::Value, conflictFunc::ConflictFunc = addConflictDefault #= Used to resolve conflicts. =#) ::Tree
    local tree::Tree = inTree
    tree = begin
        local key::Key
        local value::Value
        local key_comp::ModelicaInteger
        local outTree::Tree
        #=  Empty tree.
        =#
        @match tree begin
            EMPTY(__)  => begin
                LEAF(inKey, inValue)
            end

            NODE(key = key)  => begin
                key_comp = keyCompare(inKey, key)
                if key_comp == (-1)
                    left = add(tree.left, inKey, inValue, conflictFunc)
                    tree = NODE(tree.key, tree.value, tree.height, left, tree.right)
                elseif key_comp == 1
                    right = add(tree.right, inKey, inValue, conflictFunc)
                    tree = NODE(tree.key, tree.value, tree.height, tree.left, right)
                else
                    value = conflictFunc(inValue, tree.value, key)
                    if ! referenceEq(tree.value, value)
                        tree = NODE(tree.key, value, tree.height, tree.left, tree.right)
                    end
                end
                if key_comp == 0
                    tree
                else
                    balance(tree)
                end
            end

            LEAF(key = key)  => begin
                key_comp = keyCompare(inKey, key)
                if key_comp == (-1)
                    tree = NODE(tree.key, tree.value, 2, LEAF(inKey, inValue), EMPTY())
                elseif key_comp == 1
                    tree = NODE(tree.key, tree.value, 2, EMPTY(), LEAF(inKey, inValue))
                else
                    value = conflictFunc(inValue, tree.value, key)
                    if ! referenceEq(tree.value, value)
                        tree = LEAF(tree.key, value)
                    end
                end
                if key_comp == 0
                    tree
                else
                    balance(tree)
                end
            end
        end
    end
    tree
end

#= Adds a list of key-value pairs to the tree. =#
function addList(tree::Tree, inValues::List{<:Tuple{<:Key, Value}}, conflictFunc::ConflictFunc = addConflictDefault #= Used to resolve conflicts. =#) ::Tree


    local key::Key
    local value::Value

    for t in inValues
        (key, value) = t
        tree = add(tree, key, value, conflictFunc)
    end
    tree
end

#= Alias for add that replaces the node in case of conflict. =#
function update(tree::Tree, key::Key, value::Value) ::Tree
    add(tree, key, value, addConflictReplace)
end

#= Fetches a value from the tree given a key, or fails if no value is associated
with the key. =#
function get(tree::Tree, key::Key) ::Value
    local value::Value
    local k::Key
    k = begin
        @match tree begin
            NODE(__)  => begin
                tree.key
            end

            LEAF(__)  => begin
                tree.key
            end
        end
    end
    value = begin
        @match (keyCompare(key, k), tree) begin
            (0, LEAF(__))  => begin
                tree.value
            end

            (0, NODE(__))  => begin
                tree.value
            end

            (1, NODE(__))  => begin
                get(tree.right, key)
            end

            (-1, NODE(__))  => begin
                get(tree.left, key)
            end
        end
    end
    value
end

#= Fetches a value from the tree given a key, or returns NONE if no value is
associated with the key. =#
function getOpt(tree::Tree, key::Key) ::Option{Value}
    local value::Option{Value}

    local k::Key

    k = begin
        @match tree begin
            NODE(__)  => begin
                tree.key
            end

            LEAF(__)  => begin
                tree.key
            end

            _  => begin
                key
            end
        end
    end
    value = begin
        @match (keyCompare(key, k), tree) begin
            (0, LEAF(__))  => begin
                SOME(tree.value)
            end

            (0, NODE(__))  => begin
                SOME(tree.value)
            end

            (1, NODE(__))  => begin
                getOpt(tree.right, key)
            end

            (-1, NODE(__))  => begin
                getOpt(tree.left, key)
            end

            _  => begin
                NONE()
            end
        end
    end
    value
end

#= Creates a new tree from a list of key-value pairs. =#
function fromList(inValues::List{<:Tuple{<:Key, Value}}, conflictFunc::ConflictFunc = addConflictDefault #= Used to resolve conflicts. =#) ::Tree
    local tree::Tree = EMPTY()

    local key::Key
    local value::Value

    for t in inValues
        (key, value) = t
        tree = add(tree, key, value, conflictFunc)
    end
    tree
end

#= Converts the tree to a flat list of key-value tuples. =#
function toList(inTree::Tree, lst::List{<:Tuple{<:Key, Value}} = nil) ::List{Tuple{Key, Value}}


    lst = begin
        local key::Key
        local value::Value
        @match inTree begin
            NODE(key = key, value = value)  => begin
                lst = toList(inTree.right, lst)
                lst = _cons((key, value), lst)
                lst = toList(inTree.left, lst)
                lst
            end

            LEAF(key = key, value = value)  => begin
                _cons((key, value), lst)
            end

            _  => begin
                lst
            end
        end
    end
    lst
end

#= Constructs a list of all the values in the tree. =#
function listValues(tree::Tree, lst::List{<:Value} = nil) ::List{Value}


    lst = begin
        local value::Value
        @match tree begin
            NODE(value = value)  => begin
                lst = listValues(tree.right, lst)
                lst = _cons(value, lst)
                lst = listValues(tree.left, lst)
                lst
            end

            LEAF(value = value)  => begin
                _cons(value, lst)
            end

            _  => begin
                lst
            end
        end
    end
    lst
end

#= Joins two trees by adding the second one to the first. =#
function join(tree::Tree, treeToJoin::Tree, conflictFunc::ConflictFunc = addConflictDefault #= Used to resolve conflicts. =#) ::Tree


    tree = begin
        @match treeToJoin begin
            EMPTY(__)  => begin
                tree
            end

            NODE(__)  => begin
                tree = add(tree, treeToJoin.key, treeToJoin.value, conflictFunc)
                tree = join(tree, treeToJoin.left, conflictFunc)
                tree = join(tree, treeToJoin.right, conflictFunc)
                tree
            end

            LEAF(__)  => begin
                add(tree, treeToJoin.key, treeToJoin.value, conflictFunc)
            end
        end
    end
    tree
end

#= Traverses the tree in depth-first pre-order and applies the given function to
each node, but without constructing a new tree like with mymap. =#
function forEach(tree::Tree, func::EachFunc)
    _ = begin
        @match tree begin
            NODE(__)  => begin
                forEach(tree.left, func)
                func(tree.key, tree.value)
                forEach(tree.right, func)
                ()
            end

            LEAF(__)  => begin
                func(tree.key, tree.value)
                ()
            end

            EMPTY(__)  => begin
                ()
            end
        end
    end
end

function intersection()
    fail()
end

#= Traverses the tree in depth-first pre-order and applies the given function to
each node, constructing a new tree with the resulting nodes. =#
function mymap(inTree::Tree, inFunc::MapFunc) ::Tree
    local outTree::Tree = inTree

    outTree = begin
        local key::Key
        local value::Value
        local new_value::Value
        local branch::Tree
        local new_branch::Tree
        @match outTree begin
            NODE(key = key, value = value)  => begin
                new_branch = mymap(outTree.left, inFunc)
                if ! referenceEq(new_branch, outTree.left)
                    @set outTree.left = new_branch
                end
                new_value = inFunc(key, value)
                if ! referenceEq(value, new_value)
                    @set outTree.value = new_value
                end
                new_branch = mymap(outTree.right, inFunc)
                if ! referenceEq(new_branch, outTree.right)
                    @set outTree.right = new_branch
                end
                outTree
            end

            LEAF(key = key, value = value)  => begin
                new_value = inFunc(key, value)
                if ! referenceEq(value, new_value)
                    @set outTree.value = new_value
                end
                outTree
            end

            _  => begin
                inTree
            end
        end
    end
    outTree
end

#= Traverses the tree in depth-first pre-order and applies the given function to
each node, in the process updating the given argument. =#
function fold(inTree::Tree, inFunc::FoldFunc, inStartValue::FT)  where {FT}
    local outResult::FT = inStartValue

    outResult = begin
        local key::Key
        local value::Value
        @match inTree begin
            NODE(key = key, value = value)  => begin
                outResult = fold(inTree.left, inFunc, outResult)
                outResult = inFunc(key, value, outResult)
                outResult = fold(inTree.right, inFunc, outResult)
                outResult
            end

            LEAF(key = key, value = value)  => begin
                outResult = inFunc(key, value, outResult)
                outResult
            end

            _  => begin
                outResult
            end
        end
    end
    outResult
end

#= Like fold, but takes two fold arguments. =#
function fold_2(tree::Tree, foldFunc::FoldFunc, foldArg1::FT1, foldArg2::FT2)  where {FT1, FT2}



    () = begin
        @match tree begin
            NODE(__)  => begin
                (foldArg1, foldArg2) = fold_2(tree.left, foldFunc, foldArg1, foldArg2)
                (foldArg1, foldArg2) = foldFunc(tree.key, tree.value, foldArg1, foldArg2)
                (foldArg1, foldArg2) = fold_2(tree.right, foldFunc, foldArg1, foldArg2)
                ()
            end

            LEAF(__)  => begin
                (foldArg1, foldArg2) = foldFunc(tree.key, tree.value, foldArg1, foldArg2)
                ()
            end

            _  => begin
                ()
            end
        end
    end
    (foldArg1, foldArg2)
end

#= Like fold, but if the fold function returns false it will not continue down
into the tree (but will still continue with other branches). =#
function foldCond(tree::Tree, foldFunc::FoldFunc, value::FT)  where {FT}


    value = begin
        local c::Bool
        @match tree begin
            NODE(__)  => begin
                (value, c) = foldFunc(tree.key, tree.value, value)
                if c
                    value = foldCond(tree.left, foldFunc, value)
                    value = foldCond(tree.right, foldFunc, value)
                end
                value
            end

            LEAF(__)  => begin
                (value, c) = foldFunc(tree.key, tree.value, value)
                value
            end

            _  => begin
                value
            end
        end
    end
    value
end

#= Traverses the tree in depth-first pre-order and applies the given function to
each node, constructing a new tree with the resulting nodes. mapFold also
takes an extra argument which is updated on each call to the given function. =#
function mapFold(inTree::Tree, inFunc::MapFunc, inStartValue::FT)  where {FT}
    local outResult::FT = inStartValue
    local outTree::Tree = inTree

    outTree = begin
        local key::Key
        local value::Value
        local new_value::Value
        local branch::Tree
        local new_branch::Tree
        @match outTree begin
            NODE(key = key, value = value)  => begin
                (new_branch, outResult) = mapFold(outTree.left, inFunc, outResult)
                if ! referenceEq(new_branch, outTree.left)
                    outTree.left = new_branch
                end
                (new_value, outResult) = inFunc(key, value, outResult)
                if ! referenceEq(value, new_value)
                    outTree.value = new_value
                end
                (new_branch, outResult) = mapFold(outTree.right, inFunc, outResult)
                if ! referenceEq(new_branch, outTree.right)
                    outTree.right = new_branch
                end
                outTree
            end

            LEAF(key = key, value = value)  => begin
                (new_value, outResult) = inFunc(key, value, outResult)
                if ! referenceEq(value, new_value)
                    outTree.value = new_value
                end
                outTree
            end

            _  => begin
                inTree
            end
        end
    end
    (outTree, outResult)
end

function setTreeLeftRight(orig::Tree, left::Tree = EMPTY(), right::Tree = EMPTY()) ::Tree
    local res::Tree

    res = begin
        @match (orig, left, right) begin
            (NODE(__), EMPTY(__), EMPTY(__))  => begin
                LEAF(orig.key, orig.value)
            end

            (LEAF(__), EMPTY(__), EMPTY(__))  => begin
                orig
            end

            (NODE(__), _, _)  => begin
                if referenceEqOrEmpty(orig.left, left) && referenceEqOrEmpty(orig.right, right)
                    orig
                else
                    NODE(orig.key, orig.value, max(height(left), height(right)) + 1, left, right)
                end
            end

            (LEAF(__), _, _)  => begin
                NODE(orig.key, orig.value, max(height(left), height(right)) + 1, left, right)
            end
        end
    end
    res
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end
