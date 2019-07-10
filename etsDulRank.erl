%%%-------------------------------------------------------------------
%%% @author huyuwei01
%%% @copyright (C) 2019, <COMPANY>
%%% @doc
%%% ets为基础的双向链表,根据M:F(Item)返回的值从小到大排序
%%% 数据量比较大, 频繁修改和删除, 又需要有序排列的时候使用
%%%
%%% 原理:根据2分法,分割数据,每块50个数据
%%%
%%% 性能测试 500W条数据插入,此模块和单纯的ets对比
%%% 此模块时125秒,ETS耗时7秒
%%% @end
%%% Created : 09. 一月 2019 15:29
%%%-------------------------------------------------------------------
-module(etsDulRank).
-author("huyuwei01").

%% API
-export([
    new/2,
    new/3,
    get/2,
    insert/2,
    del/2,
    size/1,
    from_list/2,
    foldl/3, foldr/3, for_next/4, for_prior/4,
    get_start/1, get_end/1, get_next/2, get_prior/2,
    get_by_rank/2, get_rank/2,
    sublist/3, sublistDesc/3,
    notSortUpdate/2,
    clear/1
]).
%% 测试用
-export([test/0, f/1, test2/0, testSort/1]).

-record(dulNode, {k, v, s, prior, next}).
-define(RankInfo, dulNodeScore).
-define(MainTreeKey, dulNodeMainTreeKey).
-define(TreeKey, dulNodeTreeKey).
-define(MaxDataNum, 50). %% 最低层树最大数据量

-record(infoRecord, {k = ?RankInfo, m, f, keypos, startKey, endKey, size=0, uniqueId=0}).
-record(treeRecord, {k, v, size, minScore, maxScore}).

%% {M,F} 分值函数,根据该函数返回的分值,从小到大排序
new(EtsName, Keypos, {M, F}) ->
    ets:new(EtsName, [set, protected, named_table, {keypos, #dulNode.k}, {read_concurrency, true}]),
    ets:insert(EtsName, #infoRecord{m = M, f = F, keypos = Keypos}),
    EtsName.

new(Keypos, {M, F}) ->
    Ets = ets:new(aaa, [set, protected, {keypos, #dulNode.k}, {read_concurrency, true}]),
    ets:insert(Ets, #infoRecord{m = M, f = F, keypos = Keypos}),
    Ets.

get(EtsName, Key) ->
    case ets:lookup(EtsName, Key) of
        [Node] ->
            Node#dulNode.v;
        _ ->
            undefined
    end.

insert(EtsName, Item) ->
    [Info] = ets:lookup(EtsName, ?RankInfo),
    insert(EtsName, Item, Info).

insert(EtsName, Item, #infoRecord{m = M, f = F, keypos = Keypos} = Info) ->
    Key = element(Keypos, Item),
    Score = M:F(Item),
    case ets:lookup(EtsName, Key) of
        [OldNode] ->
            Insert = del(EtsName, Key, OldNode, Info, []),
            case Insert of
                [] ->
                    ok;
                _ ->
                    ets:insert(EtsName, Insert)
            end,
            insert(EtsName, Item);
        _ ->
            case Info#infoRecord.size of
                0 ->
                    Insert = insert_prior(EtsName, Key, Item, Score, undefined, Info, [#treeRecord{k = {?TreeKey, ?MainTreeKey}, v=[{Score, Key}], size=1, minScore=Score, maxScore=Score}]),
                    ets:insert(EtsName, Insert);
                _ ->
                    [Tree] = ets:lookup(EtsName, {?TreeKey, ?MainTreeKey}),
                    Insert = insert2(EtsName, Tree, Score, Key, Item, Info, []),
                    ets:insert(EtsName, Insert)
            end
    end,
    ok.

insert2(EtsName, Tree, Score, Key, Item, Info, Insert) ->
    case Tree of
        %% 比现在分数还要小
        #treeRecord{v=V, size=Size, minScore=MinScore, maxScore = MaxScore} when Score < MinScore ->
            case V of
                {AKey, _} ->
                    [ATree] = ets:lookup(EtsName, {?TreeKey, AKey}),
                    insert2(EtsName, ATree, Score, Key, Item, Info, [Tree#treeRecord{size = Size + 1, minScore = Score} | Insert]);
                List when Size =:= ?MaxDataNum-1 ->
                    MaxDataNumDiv = ?MaxDataNum div 2,
                    {AList, BList} = lists:split(MaxDataNumDiv - 1, List),
                    {Info2, Akey} = getUniqueId(Info),
                    {Info3, Bkey} = getUniqueId(Info2),
                    {AMaxScore, _} = lists:last(AList),
                    {BMinScore, _} = lists:nth(1, BList),
                    Insert2 = [
                        Tree#treeRecord{v = {Akey, Bkey}, size = Size + 1, minScore = Score},
                        #treeRecord{k = {?TreeKey, Akey},  v = [{Score, Key} | AList], size = MaxDataNumDiv, minScore = Score, maxScore = AMaxScore},
                        #treeRecord{k = {?TreeKey, Bkey},  v = BList, size = MaxDataNumDiv, minScore = BMinScore, maxScore = MaxScore}
                    | Insert],
                    {_, NextKey} = lists:nth(1, AList),
                    insert_prior(EtsName, Key, Item, Score, NextKey, Info3, Insert2);
                List ->
                    [{_, NextKey} | _] = List,
                    insert_prior(EtsName, Key, Item, Score, NextKey, Info, [Tree#treeRecord{v = [{Score, Key} | List], size = Size + 1, minScore = Score} | Insert])
            end;
        %% 在分数范围内
        #treeRecord{v=V, size=Size, minScore=MinScore, maxScore = MaxScore} when Score < MaxScore ->
            case V of
                {AKey, BKey} ->
                    Insert2 = [Tree#treeRecord{size = Size + 1} | Insert],
                    case ets:lookup(EtsName, {?TreeKey, AKey}) of
                        [#treeRecord{maxScore=AMaxScore} = ATree] when Score < AMaxScore ->
                            insert2(EtsName, ATree, Score, Key, Item, Info, Insert2);
                        _ ->
                            [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                            insert2(EtsName, BTree, Score, Key, Item, Info, Insert2)
                    end;
                List ->
                    Fun =
                        fun({S, K}, {NextKey, AccList}) ->
                            case NextKey =:= undefined andalso Score < S of
                                true ->
                                    {K, [{S, K}, {Score, Key} | AccList]};
                                _ ->
                                    {NextKey, [{S, K} | AccList]}
                            end
                        end,
                    {NextKey, List2} = lists:foldl(Fun, {undefined, []}, List),
                    List3 = lists:reverse(List2),
                    {EndInfo, EndInsert} =
                        case Size + 1 of
                            ?MaxDataNum ->
                                MaxDataNumDiv = ?MaxDataNum div 2,
                                {AList, BList} = lists:split(MaxDataNumDiv, List3),
                                {Info2, Akey} = getUniqueId(Info),
                                {Info3, Bkey} = getUniqueId(Info2),
                                {AMaxScore, _} = lists:last(AList),
                                {BMinScore, _} = lists:nth(1, BList),
                                Insert2 =[
                                    Tree#treeRecord{v = {Akey, Bkey}, size = Size + 1},
                                    #treeRecord{k = {?TreeKey, Akey},  v = AList, size = MaxDataNumDiv, minScore = MinScore, maxScore = AMaxScore},
                                    #treeRecord{k = {?TreeKey, Bkey},  v = BList, size = MaxDataNumDiv, minScore = BMinScore, maxScore = MaxScore}
                                    | Insert],
                                {Info3, Insert2};
                            _ ->
                                {Info, [Tree#treeRecord{v = List3, size = Size + 1} | Insert]}
                        end,
                    insert_prior(EtsName, Key, Item, Score, NextKey, EndInfo, EndInsert)
            end;
        %% 比现在分数还要大
        #treeRecord{v=V, size=Size, minScore=MinScore} ->
            case V of
                {_, BKey} ->
                    [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                    insert2(EtsName, BTree, Score, Key, Item, Info, [Tree#treeRecord{size = Size + 1, maxScore = Score} | Insert]);
                List when Size =:= ?MaxDataNum-1 ->
                    MaxDataNumDiv = ?MaxDataNum div 2,
                    {AList, BList} = lists:split(MaxDataNumDiv, List),
                    {Info2, Akey} = getUniqueId(Info),
                    {Info3, Bkey} = getUniqueId(Info2),
                    {AMaxScore, _} = lists:last(AList),
                    {BMinScore, _} = lists:nth(1, BList),
                    Insert2 = [
                        Tree#treeRecord{v = {Akey, Bkey}, size = Size + 1, maxScore = Score},
                        #treeRecord{k = {?TreeKey, Akey}, v = AList, size = MaxDataNumDiv, minScore = MinScore, maxScore = AMaxScore},
                        #treeRecord{k = {?TreeKey, Bkey}, v = BList ++ [{Score, Key}], size = MaxDataNumDiv, minScore = BMinScore, maxScore = Score}
                    | Insert],
                    {_, PriorKey} = lists:last(BList),
                    insert_next(EtsName, Key, Item, Score, PriorKey, Info3, Insert2);
                List ->
                    {_, PriorKey} = lists:last(List),
                    insert_next(EtsName, Key, Item, Score, PriorKey, Info, [Tree#treeRecord{v = List ++ [{Score, Key}], size = Size + 1, maxScore = Score} | Insert])
            end
    end.

%% Start从0开始算
sublist(EtsName, Start, Num) ->
    Size = etsDulRank:size(EtsName),
    case Start >= Size of
        true ->
            [];
        _ ->
            {Start1, Num1} =
                case Start + Num =< Size of
                    true ->
                        {Start + Num, Num};
                    false ->
                        {Size, Size - Start}
                end,
            case get_node_by_rank(EtsName, Start1) of
                undefined ->
                    [];
                Node ->
                    case Num1 of
                        1 ->
                            [Node#dulNode.v];
                        _ ->
                            Fun =
                                fun(_, {List, CurNode}) ->
                                    [PriorNode] = ets:lookup(EtsName, CurNode#dulNode.prior),
                                    {[PriorNode#dulNode.v | List], PriorNode}
                                end,
                            {List, _} = for(2, Num1, 1, Fun, {[Node#dulNode.v], Node}),
                            List
                    end
            end
    end.

%% Start从0开始算
sublistDesc(EtsName, Start, Num) ->
    Size = etsDulRank:size(EtsName),
    case Start >= Size of
        true ->
            [];
        _ ->
            {Start1, Num1} =
                case Start + Num =< Size of
                    true ->
                        {Size - Start - Num + 1, Num};
                    false ->
                        {1, Size - Start}
                end,
            case get_node_by_rank(EtsName, Start1) of
                undefined ->
                    [];
                Node ->
                    case Num1 of
                        1 ->
                            [Node#dulNode.v];
                        _ ->
                            Fun =
                                fun(_, {List, CurNode}) ->
                                    [PriorNode] = ets:lookup(EtsName, CurNode#dulNode.next),
                                    {[PriorNode#dulNode.v | List], PriorNode}
                                end,
                            {List, _} = for(2, Num1, 1, Fun, {[Node#dulNode.v], Node}),
                            List
                    end
            end
    end.

-spec notSortUpdate(EtsName, Item) -> true | false when
    EtsName :: atom(),
    Item :: tuple().
%% 更新与排序无关的数据(一定要确定更新的数据和排名是无关的,否则造成排序错乱)
notSortUpdate(EtsName, Item) ->
    Keypos = ets:lookup_element(EtsName, ?RankInfo, #infoRecord.keypos),
    Key = element(Keypos, Item),
    case ets:lookup(EtsName, Key) of
        [Node] ->
            ets:insert(EtsName, Node#dulNode{v = Item});
        _ ->
            false
    end.

get_rank(EtsName, Key) ->
    case ets:lookup(EtsName, Key) of
        [#dulNode{s = Score}] ->
            [Tree] = ets:lookup(EtsName, {?TreeKey, ?MainTreeKey}),
            get_rank(EtsName, Score, Tree, 0);
        _ ->
            0
    end.

get_rank(EtsName, Score, Tree, Rank) ->
    case Tree#treeRecord.v of
        {AKey, BKey} ->
            case ets:lookup(EtsName, {?TreeKey, AKey}) of
                [#treeRecord{size = Size, minScore = MaxScore} = ATree] when Score =< MaxScore ->
                    case get_rank(EtsName, Score, ATree, Rank) of
                        false ->
                            [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                            get_rank(EtsName, Score, BTree, Rank - Size) + Size;
                        Rank1 ->
                            Rank1
                    end;
                [#treeRecord{size = Size}] ->
                    [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                    get_rank(EtsName, Score, BTree, Rank) + Size
            end;
        List ->
            Fun =
                fun({S, _}, {_, A}) ->
                    case S of
                        Score ->
                            throw(A);
                        _ ->
                            {false, A + 1}
                    end
                end,
            case catch lists:foldl(Fun, {false, 1}, List) of
                {_, _} ->
                    false;
                A ->
                    A + Rank
            end
    end.

get_by_rank(EtsName, Rank) ->
    #dulNode{v = V} = get_node_by_rank(EtsName, Rank),
    V.

get_node_by_rank(EtsName, Rank) ->
    case ets:lookup(EtsName, {?TreeKey, ?MainTreeKey}) of
        [] ->
            undefined;
        [Tree] ->
            get_node_by_rank(EtsName, Rank, Tree)
    end.

get_node_by_rank(EtsName, Rank, Tree) ->
    case Tree of
        #treeRecord{v = V, size = Size} when Rank =< Size ->
            case V of
                {AKey, BKey} ->
                    case ets:lookup(EtsName, {?TreeKey, AKey}) of
                        [#treeRecord{size = ASize} = ATree] when  Rank =< ASize ->
                            get_node_by_rank(EtsName, Rank, ATree);
                        [#treeRecord{size = ASize}] ->
                            [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                            get_node_by_rank(EtsName, Rank - ASize, BTree)
                    end;
                List ->
                    {_, NodeKey} = lists:nth(Rank, List),
                    [Node] = ets:lookup(EtsName, NodeKey),
                    Node
            end;
        _ ->
            undefined
    end.

%% 插入到某个TK的前面
insert_prior(EtsName, K, V, S, TK, Info, Insert) ->
    case Info#infoRecord.size of
        0 ->
            [
                Info#infoRecord{size = 1, startKey = K, endKey = K},
                #dulNode{k=K, v=V, s=S}
                | Insert
            ];
        Size ->
                case ets:lookup(EtsName, TK) of
                    [#dulNode{prior = undefined} = T] -> %% 第一个
                        [
                            Info#infoRecord{size = Size + 1, startKey = K},
                            T#dulNode{prior = K},
                            #dulNode{k=K, v=V, s=S, next = TK}
                        | Insert];
                    [#dulNode{prior = PriorKey} = T] ->
                        [Prior] = ets:lookup(EtsName, PriorKey),
                        [
                            Info#infoRecord{size = Size + 1},
                            Prior#dulNode{next = K},
                            T#dulNode{prior = K},
                            #dulNode{k=K, v=V, s=S, prior = PriorKey, next = TK}
                        | Insert]
                end
    end.

%% 插入到某个TK的后面
insert_next(EtsName, K, V, S, TK, Info, Insert) ->
    case Info#infoRecord.size of
        0 ->
            [
                Info#infoRecord{size = 1, startKey = K, endKey = K},
                #dulNode{k=K, v=V, s=S}
                | Insert
            ];
        Size ->
            case ets:lookup(EtsName, TK) of
                [#dulNode{next = undefined} = T] -> %% 最后一个
                    [
                        Info#infoRecord{size = Size + 1, endKey = K},
                        T#dulNode{next = K},
                        #dulNode{k=K, v=V, s=S, prior = TK}
                    | Insert];
                [#dulNode{next = NextKey} = T] ->
                    [Next] = ets:lookup(EtsName, NextKey),
                    [
                        Info#infoRecord{size = Size + 1},
                        Next#dulNode{prior = K},
                        T#dulNode{next = K},
                        #dulNode{k=K, v=V, s=S, prior = TK, next = NextKey}
                    | Insert]
            end
    end.

del(EtsName, Key) ->
    case ets:lookup(EtsName, Key) of
        [Node] ->
            [Info] = ets:lookup(EtsName, ?RankInfo),
            Insert = del(EtsName, Key, Node, Info, []),
            ets:insert(EtsName, Insert),
            true;
        _ ->
            false
    end.

%% 删除一个
del(EtsName, K, Node, Info, Insert) ->
    case Info#infoRecord.size of
        1 ->
            clear(EtsName),
            [];
        Size ->
            Insert2 =
                case Node of
                    #dulNode{k = K, prior = undefined, next = NextKey} -> %% 第一个
                        [Next] = ets:lookup(EtsName, NextKey),
                        [Info#infoRecord{startKey = NextKey, size = Size - 1}, Next#dulNode{prior = undefined} | Insert];
                    #dulNode{k = K, prior = PriorKey, next = undefined} -> %% 最后一个
                        [Prior] = ets:lookup(EtsName, PriorKey),
                        [Info#infoRecord{endKey = PriorKey, size = Size - 1}, Prior#dulNode{next = undefined} | Insert];
                    #dulNode{k = K, prior = PriorKey, next = NextKey} ->
                        [Prior] = ets:lookup(EtsName, PriorKey),
                        [Next] = ets:lookup(EtsName, NextKey),
                        [Info#infoRecord{endKey = PriorKey, size = Size - 1},
                            Prior#dulNode{next = NextKey},
                            Next#dulNode{prior = PriorKey}
                            | Insert]
                end,
            ets:delete(EtsName, K),
            [Tree] = ets:lookup(EtsName, {?TreeKey, ?MainTreeKey}),
            delTree(EtsName, K, Node, Tree, Insert2)
    end.

delTree(EtsName, K, Node, Tree, Insert) ->
    Score = Node#dulNode.s,
    #treeRecord{v = V, size = Size} = Tree,
    NewSize = Size - 1,
    case V of
        {AKey, BKey} ->
            case Size of
                ?MaxDataNum -> %% 需要合并
                    [#treeRecord{v = Av}] = ets:lookup(EtsName, {?TreeKey, AKey}),
                    [#treeRecord{v = Bv}] = ets:lookup(EtsName, {?TreeKey, BKey}),
                    List2 = Av ++ Bv,
                    List3 = lists:keydelete(K, #treeRecord.k, List2),
                    ets:delete(EtsName, {?TreeKey, AKey}),
                    ets:delete(EtsName, {?TreeKey, BKey}),
                    {NewMinScore, _} = lists:nth(1, List3),
                    {NewMaxScore, _} = lists:last(List3),
                    [Tree#treeRecord{v=List3, size = NewSize, minScore = NewMinScore, maxScore = NewMaxScore} | Insert];
                _ ->
                    [ATree] = ets:lookup(EtsName, {?TreeKey, AKey}),
                    case ATree of
                        #treeRecord{maxScore = AMaxScore} when Score =< AMaxScore ->
                            case delTree(EtsName, K, Node, ATree, Insert) of
                                false ->
                                    [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                                    case delTree(EtsName, K, Node, BTree, Insert) of
                                        false ->
                                            false;
                                        L ->
                                            [BTree2 | _] = L,
                                            [Tree#treeRecord{size = NewSize, maxScore = BTree2#treeRecord.maxScore} | L]
                                    end;
                                L ->
                                    [ATree2 | _] = L,
                                    [Tree#treeRecord{size = NewSize, minScore = ATree2#treeRecord.minScore} | L]
                            end;
                        _ ->
                            [BTree] = ets:lookup(EtsName, {?TreeKey, BKey}),
                            case delTree(EtsName, K, Node, BTree, Insert) of
                                false ->
                                    false;
                                L ->
                                    [BTree2 | _] = L,
                                    [Tree#treeRecord{size = NewSize, maxScore = BTree2#treeRecord.maxScore} | L]
                            end
                    end
            end;
        List ->
            List2 = lists:keydelete(K, 2, List),
            {NewMinScore, _} = lists:nth(1, List2),
            {NewMaxScore, _} = lists:last(List2),
            [Tree#treeRecord{v=List2, size = NewSize, minScore = NewMinScore, maxScore = NewMaxScore} | Insert]
    end.




size(EtsName) ->
    case ets:lookup(EtsName, ?RankInfo) of
        [#infoRecord{size = Size}] ->
            Size;
        _ ->
            0
    end.

%% 正序循环
foldl(EtsName, Fun, Acc) ->
    case ets:lookup(EtsName, ?RankInfo) of
        [#infoRecord{startKey = StartKey}] ->
            [Start] = ets:lookup(EtsName, StartKey),
            for_next(EtsName, Fun, Acc, Start);
        _ ->
            Acc
    end.

%% 逆序循环
foldr(EtsName, Fun, Acc) ->
    case ets:lookup(EtsName, ?RankInfo) of
        [#infoRecord{endKey = EndKey}] ->
            [End] = ets:lookup(EtsName, EndKey),
            for_prior(EtsName, Fun, Acc, End);
        undefined ->
            Acc
    end.

for_next(EtsName, Fun, Acc, Cur) ->
    case Cur of
        #dulNode{k = K, v = V, next = undefined} ->
            Fun(K, V, Acc);
        #dulNode{k = K, v = V, next = NextKey} ->
            [Next] = ets:lookup(EtsName, NextKey),
            for_next(EtsName, Fun, Fun(K, V, Acc), Next)
    end.

for_prior(EtsName, Fun, Acc, Cur) ->
    case Cur of
        #dulNode{k = K, v = V, prior = undefined} ->
            Fun(K, V, Acc);
        #dulNode{k = K, v = V, prior = PriorKey} ->
            [Prior] = ets:lookup(EtsName, PriorKey),
            for_prior(EtsName, Fun, Fun(K, V, Acc), Prior)
    end.

get_start(EtsName) ->
    case ets:lookup(EtsName, ?RankInfo) of
        [#infoRecord{startKey = Key, size = Size}] when Size > 0 ->
            [#dulNode{k = K, v = V}] = ets:lookup(EtsName, Key),
            {K, V};
        _ ->
            undefined
    end.

get_end(EtsName) ->
    case ets:lookup(EtsName, ?RankInfo) of
        [#infoRecord{endKey = Key, size = Size}] when Size > 0 ->
            [#dulNode{k = K, v = V}] = ets:lookup(EtsName, Key),
            {K, V};
        _ ->
            undefined
    end.

get_next(EtsName, CurKey) ->
    case ets:lookup(EtsName, CurKey) of
        [#dulNode{next = undefined}] ->
            undefined;
        [#dulNode{next = NextKey}] ->
            [#dulNode{k = K, v = V}] = ets:lookup(EtsName, NextKey),
            {K, V};
        _ ->
            undefined
    end.

get_prior(EtsName, CurKey) ->
    case ets:lookup(EtsName, CurKey) of
        [#dulNode{prior = undefined}] ->
            undefined;
        [#dulNode{prior = PriorKey}] ->
            [#dulNode{k = K, v = V}] = ets:lookup(EtsName, PriorKey),
            {K, V};
        _ ->
            undefined
    end.

%% 从列表初始化 此函数需要优化,以后再处理
%% List = [#xxx{key, ...}]
from_list(EtsName, List) ->
    clear(EtsName),
    case length(List) of
        0 ->
            ok;
        _ ->
%%            [#infoRecord{m = M, f = F, keypos = Keypos} = Info] = ets:lookup(EtsName, ?RankInfo),
            [insert(EtsName, Item) || Item <- List]
    end,
    ok.

%% 创建树
createTree(EtsName, List, Len, TreeKey, Info, Insert) ->
    case Len < ?MaxDataNum of
        true ->
            {MinScore, _} = lists:nth(1, List),
            {MaxScore, _} = lists:last(List),
            {Info, [#treeRecord{k = {?TreeKey, TreeKey}, v=List, size = Len, minScore = MinScore, maxScore = MaxScore} | Insert]};
        _ ->
            {MinScore, _} = lists:nth(1, List),
            {MaxScore, _} = lists:last(List),
            ALen = trunc(Len/2),
            BLen = Len - ALen,
            {AList, BList} = lists:split(ALen, List),
            {Info2, Akey} = getUniqueId(Info),
            {Info3, Bkey} = getUniqueId(Info2),
            {Info4, Insert2} = createTree(EtsName, AList, ALen, Akey, Info3, Insert),
            {Info5, Insert3} = createTree(EtsName, BList, BLen, Bkey, Info4, Insert2),
            {Info5, [#treeRecord{k = {?TreeKey, TreeKey}, v = {Akey, Bkey}, size = Len, minScore = MinScore, maxScore = MaxScore} | Insert3]}
    end.

%% 删除所有
clear(EtsName) ->
    case ets:lookup(EtsName, ?RankInfo) of
        [#infoRecord{size = 0}] ->
            ok;
        [Info] ->
            ets:delete_all_objects(EtsName),
            ets:insert(EtsName, Info#infoRecord{startKey = undefined, endKey = undefined, size=0, uniqueId=0});
        _ ->
            ets:delete_all_objects(EtsName)
    end,
    ok.

%%%%%%%%%%%%%%%%%%% 内部工具类 %%%%%%%%%%%%%%%%%%%%%%%%%

getUniqueId(#infoRecord{uniqueId = Id} = Info) ->
    {Info#infoRecord{uniqueId = Id + 1}, Id + 1}.

for(End, End, _Step, Fun, AccIn) ->
    Fun(End, AccIn);
for(Start, End, Step, Fun, AccIn) ->
    for(Start+Step, End, Step, Fun, Fun(Start, AccIn)).

test() ->
    io:format("111~n"),
    new(a, 2, {?MODULE, f}),
    A = [{a, 1, 10}, {a, 2, 20}, {a, 3, 30}, {a, 4, 40}, {a, 5, 50}, {a, 6, 60}, {a, 7, 70}, {a, 8, 80}, {a, 9, 90}],
    from_list(a, A),
    io:format("222~p~n", [{etsDulRank:size(a)}]),
    ok.

%% 性能测试 500W条数据插入,此模块和单纯的ets对比
%% 此模块时125秒,ETS耗时7秒
%% eprof:start().
%% etsDulRank:test2().
%% eprof:stop_profiling().
%% eprof:analyze().

%%
%% eprof:start().
%% eprof:profile([self()], etsDulRank, test2, []).
%% eprof:stop_profiling().
%% eprof:analyze().
test2() ->

    Fun =
        fun(Index, Acc) ->
            [{Index, rand:uniform()} | Acc]
        end,
    List = common:for(1, 5000000, Fun, []),

    Time1 = mytime:getNowSeconds(),
    new(rankTest, 1, {?MODULE, testSort}),
    [insert(rankTest, Item) || Item <- List],
    Time2 = mytime:getNowSeconds(),
    io:format("~p~n", [Time2 - Time1]),

    ets:new(etsTest, [set, protected, named_table, {keypos, #dulNode.k}, {read_concurrency, true}]),
    [etsInsert(etsTest, Item) || Item <- List],
    Time3 = mytime:getNowSeconds(),
    io:format("~p~n", [Time3 - Time2]),
    ok.

etsInsert(Name, Item) ->
    ets:insert(Name, Item).

f({_, _, S}) ->
    S.

testSort({_, S}) ->
    S.
