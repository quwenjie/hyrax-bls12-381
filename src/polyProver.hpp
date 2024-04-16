//
// Created by juzix on 2021/6/4.
//

#ifndef HYRAX_P224_POLYPROVER_HPP
#define HYRAX_P224_POLYPROVER_HPP


#include "timer.hpp"
#include "utils.hpp"
#include "typedef.hpp"
#include <vector>
#include <thread>
#include <queue>
#include <mutex>
#include <condition_variable>
#include <mcl/bls12_381.hpp>

using namespace std;
using namespace mcl::bn;

namespace hyrax_bls12_381 {
    template <typename T>
class ThreadSafeQueue {
public:
    ThreadSafeQueue() {}

    void Push(T value) {
        unique_lock<mutex> lock(mutex_);
        queue_.push(value);
        lock.unlock();
        condition_variable_.notify_one();
    }

    bool TryPop(T& value) {
        lock_guard<mutex> lock(mutex_);
        if (queue_.empty()) {
            return false;
        }
        value = queue_.front();
        queue_.pop();
        return true;
    }

    void WaitPop(T& value) {
        unique_lock<mutex> lock(mutex_);
        condition_variable_.wait(lock, [this] { return !queue_.empty(); });
        value = queue_.front();
        queue_.pop();
    }

    bool Empty() const {
        lock_guard<mutex> lock(mutex_);
        return queue_.empty();
    }
    int Size() const {
        lock_guard<mutex> lock(mutex_);
        return queue_.size();
    }

private:
    mutable mutex mutex_;
    queue<T> queue_;
    condition_variable condition_variable_;
};
const int COMM_MAX=1e5;
    class polyProver {
    public:
        polyProver(const vector<Fr> &_Z,const vector<G1> &_gens);
        polyProver(const vector<int> &_Zi, const vector<G1> &_gens);
        void commit(vector<G1>& v);
        Fr parallel_evaluate(const vector<Fr> &x,int th_num=4, int dim1=0,int dim2=0) ;
        Fr fast_evaluate(const vector<Fr> &x,int th_num=4,int dim1=0,int dim2=0);
        vector<G1> commit(int thread=4);
        Fr evaluate(const vector<Fr> &x);

        double getPT() const;

        double getPS() const;

        void initBulletProve(const vector<Fr> &_lx, const vector<Fr> &_rx,int th=4);

        void bulletProve(G1 &lcomm, G1 &rcomm, Fr &ly, Fr &ry);

        void bulletUpdate(const Fr &randomness);

        Fr bulletOpen();

    private:
        vector<G1> gens;
    public:
        const vector<G1> &getGens() const;

    private:
        vector<G1> comm_Z;

        vector<Fr> Z, L, R, t;
        vector<int> Zi;
        vector<Fr> RZ;
        Fr scale;
        u8 bit_length;
        timer pt;   // s
        u64 ps;     // KB

        vector<G1> bullet_g;
        vector<Fr> bullet_a;
    };
    void MUL_VEC_bucket(G1& ret,G1* vec1,int* vec2,int n);
}


#endif //HYRAX_P224_POLYPROVER_HPP
