#include <cmath>
#include <cstring>
#include <iostream>
#include <cstdlib>
#include <ctime>
#include<vector>
#include<unordered_map>
#include<string>
#include<algorithm>
#include<climits>
#include<random>

using namespace std;

const int TIME_LIMIT = 980; // ensure completion within 1s
const int MAX_DEPTH = 8;
const int INF = 1 << 30;
int startX = -1, startY = -1, resultX = -1, resultY = -1;
int currBotColor;
int gridInfo[7][7] = { 0 };
int blackPieceCount = 2, whitePieceCount = 2;
using U64 = uint64_t;                // 49 位 bitBoard
enum Side { BLACK = 0, WHITE = 1 };

static int delta[24][2] = { { 1,1 },{ 0,1 },{ -1,1 },{ -1,0 },
{ -1,-1 },{ 0,-1 },{ 1,-1 },{ 1,0 },
{ 2,0 },{ 2,1 },{ 2,2 },{ 1,2 },
{ 0,2 },{ -1,2 },{ -2,2 },{ -2,1 },
{ -2,0 },{ -2,-1 },{ -2,-2 },{ -1,-2 },
{ 0,-2 },{ 1,-2 },{ 2,-2 },{ 2,-1 } };

// Transposition table entry
struct TTEntry
{
    int depth;
    int value;
    int flag; // 0: exact, 1: lower bound, 2: upper bound
};
struct Node { U64 b[2]; Side side; }; // 局面状态
unordered_map<size_t, TTEntry> transpositionTable;

// Hash function for board state
size_t zobristTable[7][7][3];
size_t currentHash;

U64 zobrist[2][49];
void init_zobrist()
{
    mt19937_64 rng(2023);
    for (int s = 0; s < 2; ++s)
        for (int i = 0; i < 49; ++i) zobrist[s][i] = rng();
}
void initZobrist()
{
    mt19937_64 rng(12345);
    for (int i = 0; i < 7; ++i)
        for (int j = 0; j < 7; ++j)
            for (int k = 0; k < 3; ++k)
                zobristTable[i][j][k] = rand();
}

void updateHash(int x, int y, int oldVal, int newVal)
{
    currentHash ^= zobristTable[x][y][oldVal + 1];
    currentHash ^= zobristTable[x][y][newVal + 1];
}

inline bool inMap(int x, int y)
{
    return x >= 0 && x < 7 && y >= 0 && y < 7;
}
struct Move
{
    int x0, y0, x1, y1;
    uint8_t from, to;
    Move() {};
    Move(int x0, int y0, int x1, int y1) : x0(x0), y0(y0), x1(x1), y1(y1) {}
};
struct UndoInfo
{
    vector<pair<int, int>> changed; // 每次记录哪些格子被修改了
    int blackCount, whiteCount;
    size_t hashBefore;
};
bool ProcStep(int x0, int y0, int x1, int y1, int color, bool updateHashFlag = false)
{
    if (color == 0 || !inMap(x0, y0) || !inMap(x1, y1) || gridInfo[x0][y0] != color || gridInfo[x1][y1] != 0)
        return false;
    int dx = abs(x0 - x1), dy = abs(y0 - y1);
    if ((dx == 0 && dy == 0) || dx > 2 || dy > 2)
        return false;
    if (updateHashFlag)
    {
        updateHash(x0, y0, gridInfo[x0][y0], 0);
        if (dx == 2 || dy == 2)     gridInfo[x0][y0] = 0;
        updateHash(x1, y1, 0, color);
    }
    else
        if (dx == 2 || dy == 2)  gridInfo[x0][y0] = 0;
    gridInfo[x1][y1] = color;
    if (updateHashFlag) updateHash(x1, y1, 0, color);
    int converted = 0;
    for (int dir = 0; dir < 8; ++dir)
    {
        int x = x1 + delta[dir][0], y = y1 + delta[dir][1];
        if (inMap(x, y) && gridInfo[x][y] == -color)
        {
            gridInfo[x][y] = color;
            if (updateHashFlag) updateHash(x, y, -color, color);
            converted++;
        }
    }
    if (color == 1)
    {
        blackPieceCount += (dx <= 1 && dy <= 1) ? 1 + converted : converted;
        whitePieceCount -= converted;
    }
    else
    {
        whitePieceCount += (dx <= 1 && dy <= 1) ? 1 + converted : converted;
        blackPieceCount -= converted;
    }
    return true;
}

vector<Move> getValidMoves(int color)
{
    vector<Move> moves;
    for (int x0 = 0; x0 < 7; ++x0)
    {
        for (int y0 = 0; y0 < 7; ++y0)
        {
            if (gridInfo[x0][y0] != color) continue;

            for (int dir = 0; dir < 24; ++dir)
            {
                int x1 = x0 + delta[dir][0], y1 = y0 + delta[dir][1];
                if (inMap(x1, y1) && gridInfo[x1][y1] == 0)        moves.emplace_back(x0, y0, x1, y1);
            }
        }
    }
    return moves;
}
enum GameStage { EARLY, MID, LATE };
int evaluate()
{
    int score = 0;
    // 阶段判断：前中后期
    int totalPieces = blackPieceCount + whitePieceCount;
    GameStage stage;
    if (totalPieces <= 15) stage = EARLY;
    else if (totalPieces <= 35) stage = MID;
    else stage = LATE;
    // 各阶段权重
    int pieceWeight, mobilityWeight, centerWeight, flipWeight, cornerWeight, isolatedPenaltyWeight, stableWeight, frontierPenaltyWeight;
    // 根据阶段调整权重
    switch (stage)
    {
    case EARLY:
        pieceWeight = 6;
        mobilityWeight = 5;
        centerWeight = 2;
        flipWeight = 3;
        cornerWeight = 10;
        isolatedPenaltyWeight = 8;
        stableWeight = 5;
        frontierPenaltyWeight = 2;
        break;
    case MID:
        pieceWeight = 10;
        mobilityWeight = 4;
        centerWeight = 3;
        flipWeight = 4;
        cornerWeight = 15;
        isolatedPenaltyWeight = 6;
        stableWeight = 10;
        frontierPenaltyWeight = 5;
        break;
    case LATE:
        pieceWeight = 14;
        mobilityWeight = 2;
        centerWeight = 1;
        flipWeight = 6;
        cornerWeight = 20;
        isolatedPenaltyWeight = 3;
        stableWeight = 15;
        frontierPenaltyWeight = 6;
        break;
    }
    // 1. 物料值（当前棋子数）
    int myCount = (currBotColor == 1) ? blackPieceCount : whitePieceCount;
    int oppCount = (currBotColor == 1) ? whitePieceCount : blackPieceCount;
    score += (myCount - oppCount) * pieceWeight;

    // 2. 行动力（可选步数）
    int myMobility = getValidMoves(currBotColor).size();
    int oppMobility = getValidMoves(-currBotColor).size();
    score += (myMobility - oppMobility) * mobilityWeight;

    // 3. 中心控制
    const int centerweight[7][7] =
    {
        {0, 0, 2, 2, 2, 0, 0},
        {0, 5, 8, 8, 8, 5, 0},
        {2, 8, 12, 12, 12, 8, 2},
        {2, 8, 12, 14, 12, 8, 2},
        {2, 8, 12, 12, 12, 8, 2},
        {0, 5, 8, 8, 8, 5, 0},
        {0, 0, 2, 2, 2, 0, 0}
    };
    for (int x = 0; x < 7; ++x)
        for (int y = 0; y < 7; ++y)
            if (gridInfo[x][y] == currBotColor)
                score += centerweight[x][y] * centerWeight;
            else if (gridInfo[x][y] == -currBotColor)
                score -= centerweight[x][y] * centerWeight;

    // 4. 潜在翻转（周围8格有敌方）
    int potentialFlips = 0;
    for (int x = 0; x < 7; ++x)
        for (int y = 0; y < 7; ++y)
            if (gridInfo[x][y] == currBotColor)
                for (int dir = 0; dir < 8; ++dir)
                {
                    int nx = x + delta[dir][0], ny = y + delta[dir][1];
                    if (inMap(nx, ny) && gridInfo[nx][ny] == -currBotColor)
                        potentialFlips++;
                }
    score += potentialFlips * flipWeight;

    // 5. 边角控制（角落重要）
    const int corners[4][2] = { {0, 0}, {0, 6}, {6, 0}, {6, 6} };
    for (int i = 0; i < 4; ++i)
    {
        int x = corners[i][0], y = corners[i][1];
        if (gridInfo[x][y] == currBotColor)
            score += cornerWeight;
        else if (gridInfo[x][y] == -currBotColor)
            score -= cornerWeight;
    }

    // 6. 孤立子惩罚（没有己方邻居的己方子）
    int isolatedPenalty = 0;
    for (int x = 0; x < 7; ++x)
        for (int y = 0; y < 7; ++y)
            if (gridInfo[x][y] == currBotColor)
            {
                bool hasAlly = false;
                for (int dir = 0; dir < 8; ++dir)
                {
                    int nx = x + delta[dir][0], ny = y + delta[dir][1];
                    if (inMap(nx, ny) && gridInfo[nx][ny] == currBotColor)
                    {
                        hasAlly = true;
                        break;
                    }
                }
                if (!hasAlly) isolatedPenalty++;
            }
    score -= isolatedPenalty * isolatedPenaltyWeight;
    // 7. 稳定子奖励
    int stableCount = 0;
    for (int x = 0; x < 7; ++x)
    {
        for (int y = 0; y < 7; ++y)
        {
            if (gridInfo[x][y] != currBotColor) continue;

            bool isStable = true;
            for (int dir = 0; dir < 8; ++dir)
            {
                int nx = x + delta[dir][0], ny = y + delta[dir][1];
                if (inMap(nx, ny) && gridInfo[nx][ny] == -currBotColor)
                {
                    isStable = false;
                    break;
                }
            }
            if (isStable) stableCount++;
        }
    }
    score += stableCount * stableWeight;
    // 8. 前沿子惩罚（容易被翻的子）
    int frontierPenalty = 0;
    for (int x = 0; x < 7; ++x)
    {
        for (int y = 0; y < 7; ++y)
        {
            if (gridInfo[x][y] != currBotColor) continue;

            for (int dir = 0; dir < 8; ++dir)
            {
                int nx = x + delta[dir][0], ny = y + delta[dir][1];
                // 邻居是空格则是前沿子
                if (inMap(nx, ny) && gridInfo[nx][ny] == 0)
                {
                    frontierPenalty++;
                    break;
                }
            }
        }
    }
    score -= frontierPenalty * frontierPenaltyWeight;

    return score;
}

Move killerMoves[64][2]; // depth x 2
void initKillerMoves()
{
    for (int d = 0; d < 64; d++)
    {
        killerMoves[d][0] = Move(-1, -1, -1, -1);
        killerMoves[d][1] = Move(-1, -1, -1, -1);
    }
}
int historyTable[7][7][7][7] = {}; // 历史启发式表
int alphaBeta(int depth, int alpha, int beta, bool maximizingPlayer, int startTime)
{
    if (clock() - startTime > TIME_LIMIT * CLOCKS_PER_SEC / 1000)
        return maximizingPlayer ? -INF : INF;
    // 置换表命中
    auto ttIt = transpositionTable.find(currentHash);
    if (ttIt != transpositionTable.end() && ttIt->second.depth >= depth)
    {
        if (ttIt->second.flag == 0) return ttIt->second.value;
        if (ttIt->second.flag == 1 && ttIt->second.value >= beta) return ttIt->second.value;
        if (ttIt->second.flag == 2 && ttIt->second.value <= alpha) return ttIt->second.value;
    }
    if (depth <= 0 || blackPieceCount == 0 || whitePieceCount == 0)      return evaluate();
    vector<Move> moves = getValidMoves(maximizingPlayer ? currBotColor : -currBotColor);
    if (moves.empty())     return evaluate();
    // 插入 killer moves 优先尝试
    if (depth < 64)
    {
        // 安全插入 killer moves（不修改原始 vector）
        vector<Move> prioritizedMoves;
        // 插入合法 killer move
        for (int k = 0; k < 2; ++k)
        {
            Move km = killerMoves[depth][k];
            for (const Move& m : moves)
            {
                if (m.x0 == km.x0 && m.y0 == km.y0 && m.x1 == km.x1 && m.y1 == km.y1)
                {
                    prioritizedMoves.push_back(m);
                    break;
                }
            }
        }
        // 插入剩余非 killer moves
        for (const Move& m : moves)
        {
            bool isKiller = false;
            for (const Move& km : prioritizedMoves)
            {
                if (m.x0 == km.x0 && m.y0 == km.y0 && m.x1 == km.x1 && m.y1 == km.y1)
                {
                    isKiller = true;
                    break;
                }
            }
            if (!isKiller) prioritizedMoves.push_back(m);
        }

        moves = prioritizedMoves;
    }
    // Sort moves by heuristic (better moves first)
    sort(moves.begin(), moves.end(), [&](const Move& a, const Move& b)
        {
            auto moveScore = [&](const Move& m) -> int
                {
                    int score = 0;

                    // 1. 是否是复制型（复制优于移动）
                    int dx = abs(m.x0 - m.x1), dy = abs(m.y0 - m.y1);
                    bool isCopy = (dx <= 1 && dy <= 1);
                    if (isCopy) score += 30;
                    else score -= 15;

                    // 2. 翻转敌方棋子数量
                    int flips = 0;
                    for (int dir = 0; dir < 8; ++dir)
                    {
                        int x = m.x1 + delta[dir][0], y = m.y1 + delta[dir][1];
                        if (inMap(x, y) && gridInfo[x][y] == -currBotColor)
                            flips++;
                    }
                    score += flips * 15;

                    // 3. 靠近角落（鼓励走角）
                    if ((m.x1 == 0 || m.x1 == 6) && (m.y1 == 0 || m.y1 == 6))
                        score += 20;

                    // 4. 靠近边界（鼓励控制边界）
                    if (m.x1 == 0 || m.x1 == 6 || m.y1 == 0 || m.y1 == 6)
                        score += 10;

                    // 5. 历史启发式
                    score += historyTable[m.x0][m.y0][m.x1][m.y1];

                    return score;
                };
            return moveScore(a) > moveScore(b);
        });
    //  使用 History Heuristic 再进行一次排序

    int bestValue = maximizingPlayer ? -INF : INF;
    int ttFlag = 0; // 0: exact, 1: lower bound, 2: upper bound
    int moveCount = 0;
    for (const Move& move : moves)
    {
        moveCount++;
        // Save current state
        int tempGrid[7][7];
        memcpy(tempGrid, gridInfo, sizeof(gridInfo));
        int tempBlack = blackPieceCount, tempWhite = whitePieceCount;
        size_t tempHash = currentHash;

        // Make move
        ProcStep(move.x0, move.y0, move.x1, move.y1, maximizingPlayer ? currBotColor : -currBotColor, true);

        int value = alphaBeta(depth - 1, alpha, beta, !maximizingPlayer, startTime);

        // Restore state
        memcpy(gridInfo, tempGrid, sizeof(gridInfo));
        blackPieceCount = tempBlack;
        whitePieceCount = tempWhite;
        currentHash = tempHash;

        if (maximizingPlayer)
        {
            if (value > bestValue)
            {
                bestValue = value;
                if (bestValue >= beta)
                {
                    // 记录 killer move
                    if (!(killerMoves[depth][0].x0 == move.x0 && killerMoves[depth][0].y0 == move.y0 && killerMoves[depth][0].x1 == move.x1 && killerMoves[depth][0].y1 == move.y1))
                    {
                        killerMoves[depth][1] = killerMoves[depth][0];
                        killerMoves[depth][0] = move;
                    }
                    // 更新 History Heuristic
                    historyTable[move.x0][move.y0][move.x1][move.y1] += 1 << depth;
                    ttFlag = 1;  // lower bound
                    break;
                }
                alpha = max(alpha, bestValue);
            }
        }
        else
        {
            if (value < bestValue)
            {
                bestValue = value;
                if (bestValue <= alpha)
                {
                    // 记录 killer move
                    if (!(killerMoves[depth][0].x0 == move.x0 && killerMoves[depth][0].y0 == move.y0 && killerMoves[depth][0].x1 == move.x1 && killerMoves[depth][0].y1 == move.y1))
                    {
                        killerMoves[depth][1] = killerMoves[depth][0];
                        killerMoves[depth][0] = move;
                    }
                    //  更新 History Heuristic
                    historyTable[move.x0][move.y0][move.x1][move.y1] += 1 << depth;
                    ttFlag = 2;  // upper bound
                    break;
                }
                beta = min(beta, bestValue);
            }
        }
    }

    // Store in transposition table
    transpositionTable[currentHash] = { depth, bestValue, ttFlag };

    return bestValue;
}

Move findBestMove(int startTime)
{
    vector<Move> moves = getValidMoves(currBotColor);
    if (moves.empty()) return Move(-1, -1, -1, -1);

    Move bestMove = moves[0];
    int bestValue = -INF;
    int depth = 1;

    initZobrist();
    currentHash = 0;
    for (int x = 0; x < 7; ++x)
        for (int y = 0; y < 7; ++y)
            currentHash ^= zobristTable[x][y][gridInfo[x][y] + 1];

    // Iterative deepening
    while (clock() - startTime < TIME_LIMIT * CLOCKS_PER_SEC / 1000 && depth <= MAX_DEPTH)
    {
        int currentBestValue = -INF;
        Move currentBestMove = moves[0];

        for (Move& move : moves)
        {
            // Save state
            int tempGrid[7][7];
            memcpy(tempGrid, gridInfo, sizeof(gridInfo));
            int tempBlack = blackPieceCount, tempWhite = whitePieceCount;
            size_t tempHash = currentHash;

            // Make move
            ProcStep(move.x0, move.y0, move.x1, move.y1, currBotColor, true);

            int value = alphaBeta(depth - 1, -INF, INF, false, startTime);

            // Restore state
            memcpy(gridInfo, tempGrid, sizeof(gridInfo));
            blackPieceCount = tempBlack;
            whitePieceCount = tempWhite;
            currentHash = tempHash;

            if (value > currentBestValue)
            {
                currentBestValue = value;
                currentBestMove = move;
            }

            if (clock() - startTime > TIME_LIMIT * CLOCKS_PER_SEC / 1000)
                break;
        }

        if (currentBestValue > bestValue)
        {
            bestValue = currentBestValue;
            bestMove = currentBestMove;
        }

        depth++;
    }

    return bestMove;
}

int main()
{
    istream::sync_with_stdio(false);
    int x0, y0, x1, y1;
    // 初始化棋盘
    gridInfo[0][0] = gridInfo[6][6] = 1;  //|黑|白|
    gridInfo[6][0] = gridInfo[0][6] = -1; //|白|黑|
    // 分析自己收到的输入和自己过往的输出，并恢复状态
    int turnID;
    currBotColor = -1; // 第一回合收到坐标是-1, -1，说明我是黑方
    cin >> turnID;
    for (int i = 0; i < turnID - 1; i++)
    {
        // 根据这些输入输出逐渐恢复状态到当前回合
        cin >> x0 >> y0 >> x1 >> y1;
        if (x1 >= 0)    	ProcStep(x0, y0, x1, y1, -currBotColor); // 模拟对方落子
        else	   currBotColor = 1;
        cin >> x0 >> y0 >> x1 >> y1;
        if (x1 >= 0)		ProcStep(x0, y0, x1, y1, currBotColor); // 模拟己方落子
    }
    // 看看自己本回合输入
    cin >> x0 >> y0 >> x1 >> y1;
    if (x1 >= 0) ProcStep(x0, y0, x1, y1, -currBotColor); // 模拟对方落子
    else currBotColor = 1;
    // 找出合法落子点
    int beginPos[1000][2], possiblePos[1000][2], posCount = 0, choice, dir;
    for (y0 = 0; y0 < 7; y0++)
        for (x0 = 0; x0 < 7; x0++)
        {
            if (gridInfo[x0][y0] != currBotColor)		continue;
            for (dir = 0; dir < 24; dir++)
            {
                x1 = x0 + delta[dir][0];
                y1 = y0 + delta[dir][1];
                if (!inMap(x1, y1))			continue;
                if (gridInfo[x1][y1] != 0)		continue;
                beginPos[posCount][0] = x0;
                beginPos[posCount][1] = y0;
                possiblePos[posCount][0] = x1;
                possiblePos[posCount][1] = y1;
                posCount++;
            }
        }
    // 决策部分
    int startTime = clock();
    initKillerMoves();
    // 做出决策
    if (posCount > 0)
    {
        Move bestMove = findBestMove(startTime);
        startX = bestMove.x0;
        startY = bestMove.y0;
        resultX = bestMove.x1;
        resultY = bestMove.y1;
    }
    else startX = startY = resultX = resultY = -1;
    cout << startX << " " << startY << " " << resultX << " " << resultY;
    return 0;
}