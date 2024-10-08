/*
 * file       : nfb_driver.c
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: create interprocess comunication with nfb program. This framework use POSIX queue
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


#include "nfb_driver.h"
#include <iostream>
#include <string>

#include <grpcpp/ext/proto_server_reflection_plugin.h>
#include <grpcpp/grpcpp.h>
#include <grpcpp/health_check_service_interface.h>

#include "nfb_grpc.grpc.pb.h"
extern "C" {
#include <libfdt.h>
}

///////////////////////////////////
// REQUEST CLASSES
class req_base {

public:
    typedef enum {PROCESS, FINISH} status_t;

protected :
    grpc::ServerContext ctx;
    status_t status;
    nfb_grpc::Nfb::AsyncService * service;
    grpc::ServerCompletionQueue* cq;
    req_base ** base_ptr;
    void * fdt;

public:
    req_base(req_base ** base_ptr) : base_ptr(base_ptr), fdt(NULL)
    {
    }

    virtual ~req_base()
    {
    }

    virtual void process_register(nfb_grpc::Nfb::AsyncService * service, grpc::ServerCompletionQueue* cq)
    {
    }

    virtual void get_type(unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset)
    {
        //type 0 is response
        *cmd = 0;
    }


    virtual void process(const svOpenArrayHandle out)
    {
    }

    virtual void finish()
    {
    }

    void set_fdt(void * fdt)
    {
        this->fdt = fdt;
    }

    status_t status_get()
    {
        return status;
    }

};

class req_fdt : public req_base {
private :
    nfb_grpc::nfb_rpc_device request;
    nfb_grpc::nfb_fdt        reply;
    grpc::ServerAsyncResponseWriter<nfb_grpc::nfb_fdt> responder;

public:
    req_fdt(req_base ** base_ptr) : req_base(base_ptr), responder(&ctx)
    {
        //fdt = NULL;
    }

    virtual void process_register(nfb_grpc::Nfb::AsyncService * service, grpc::ServerCompletionQueue* cq)
    {
        this->cq = cq;
        this->service = service;
        this->service->RequestNfb_fdt_get(&ctx, &request, &responder, cq, cq, this);
        status = PROCESS;
    }

    virtual void get_type(unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset)
    {
        *cmd = 0;
        if (status == PROCESS) {
            *cmd = 1;
        }
    }

    virtual void finish()
    {
        if (status == FINISH) {
            *base_ptr = new req_fdt(base_ptr);
            (*base_ptr)->set_fdt(fdt);
            (*base_ptr)->process_register(service, cq);
            delete this;
        }
    }


    virtual void process(const svOpenArrayHandle out)
    {
        if (status == PROCESS) {
            void * ptr;
            int unsigned ptr_size = 0;

            if (out != NULL) {
                ptr      = svGetArrayPtr(out);
                ptr_size = svSizeOfArray(out);
            }

            reply.set_fdt(ptr, ptr_size);
            responder.Finish(reply, grpc::Status::OK, this);
            status = FINISH;
        }
    }
};

class req_read : public req_base {
private :
    nfb_grpc::nfb_read_req  request;
    nfb_grpc::nfb_read_resp reply;
    grpc::ServerAsyncResponseWriter<nfb_grpc::nfb_read_resp> responder;

public:
    req_read(req_base ** base_ptr) : req_base(base_ptr), responder(&ctx)
    {
    }

    virtual void process_register(nfb_grpc::Nfb::AsyncService * service, grpc::ServerCompletionQueue* cq)
    {
        this->cq = cq;
        this->service = service;
        this->service->RequestNfb_comp_read(&ctx, &request, &responder, cq, cq, this);
        status = PROCESS;
    }

    virtual void get_type(unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset)
    {
        *cmd = 0;
        if (status == PROCESS) {
            uint64_t offset_tmp;
            int proplen;
            const fdt32_t *prop;


            *cmd = 3;
            prop = (fdt32_t*) fdt_getprop(fdt, request.fdt_offset(), "reg", &proplen);

            if (proplen == sizeof(*prop) * 2) {
                offset_tmp = fdt32_to_cpu(prop[0]);
            }

            *data_size = request.nbyte();
            offset_tmp += request.offset();
            offset[0].aval = offset_tmp & 0xffffffff;
            offset[0].bval = 0;
            offset[1].aval = (offset_tmp >> 32) & 0xffffffff;
            offset[1].bval = 0;
        }
    }

    virtual void finish()
    {
        if (status == FINISH) {
            *base_ptr = new req_read(base_ptr);
            (*base_ptr)->set_fdt(fdt);
            (*base_ptr)->process_register(service, cq);
            delete this;
        }
    }

    virtual void process(const svOpenArrayHandle out)
    {
        if (status == PROCESS) {
            void * ptr;
            int unsigned ptr_size = 0;

            if (out != NULL) {
                ptr      = svGetArrayPtr(out);
                ptr_size = svSizeOfArray(out);
                //memcpy(data->buff + sizeof(msg_t), ptr, ptr_size);
            }

            reply.set_status(ptr_size);
            reply.set_data(ptr, ptr_size);
            responder.Finish(reply, grpc::Status::OK, this);
            status = FINISH;
        }
    }
};


class req_write : public req_base {
private :
    nfb_grpc::nfb_write_req request;
    nfb_grpc::nfb_write_resp reply;
    grpc::ServerAsyncResponseWriter<nfb_grpc::nfb_write_resp> responder;

public:
    req_write(req_base ** base_ptr) : req_base(base_ptr), responder(&ctx)
    {
    }

    virtual void process_register(nfb_grpc::Nfb::AsyncService * service, grpc::ServerCompletionQueue* cq)
    {
        this->cq = cq;
        this->service = service;
        this->service->RequestNfb_comp_write(&ctx, &request, &responder, cq, cq, this);
        status = PROCESS;
    }

    virtual void get_type(unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset)
    {

        *cmd = 0;
        if (status == PROCESS) {
            uint64_t offset_tmp = 0;
            int proplen;
            const fdt32_t *prop;

           *cmd = 2;
            prop = (fdt32_t*) fdt_getprop(fdt, request.fdt_offset(), "reg", &proplen);

            if (proplen == sizeof(*prop) * 2) {
                offset_tmp = fdt32_to_cpu(prop[0]);
            }

            *data_size = request.nbyte();
            offset_tmp += request.offset();
            offset[0].aval = offset_tmp & 0xffffffff;
            offset[0].bval = 0;
            offset[1].aval = (offset_tmp >> 32) & 0xffffffff;
            offset[1].bval = 0;
        }
    }

    virtual void finish()
    {
         if (status == FINISH) {
            *base_ptr = new req_write(base_ptr);
            (*base_ptr)->set_fdt(fdt);
            (*base_ptr)->process_register(service, cq);
            delete this;
        }
    }

    virtual void process(const svOpenArrayHandle out)
    {
        if (status == PROCESS) {
            void * ptr;
            int unsigned ptr_size = 0;

            if (out != NULL) {
                ptr      = svGetArrayPtr(out);
                ptr_size = svSizeOfArray(out);
            }

            memcpy(ptr, request.data().c_str(), ptr_size);
            reply.set_status(ptr_size);
            responder.Finish(reply, grpc::Status::OK, this);
            status = FINISH;
        }
    }
};



class nfb_server
{
    public:
        nfb_grpc::Nfb::AsyncService service;
        grpc::ServerBuilder builder;
        std::unique_ptr<grpc::Server> server;
        std::unique_ptr<grpc::ServerCompletionQueue> cq;

    public:

        nfb_server() {
        }

        bool server_run(const char * addr, int * port) {
            builder.AddListeningPort(addr, grpc::InsecureServerCredentials(), port);
            builder.RegisterService(&service);

            cq     = builder.AddCompletionQueue();
            server = builder.BuildAndStart();

            if (cq != NULL && server != NULL) {
                return true;
            } else {
                return false;
            }
        }

        ~nfb_server() {
              if (server != NULL) {
                  server->Shutdown();
              }

              if (cq != NULL) {
                  void * tag;
                  bool ok;
                  grpc::CompletionQueue::NextStatus st_ret;
                  gpr_timespec deadline;

                  deadline.clock_type = GPR_TIMESPAN;
                  deadline.tv_sec = 0;
                  deadline.tv_nsec = 0; // NOWAIT
                  while ((st_ret = cq->AsyncNext<gpr_timespec>(&tag, &ok, deadline)) == grpc::CompletionQueue::NextStatus::GOT_EVENT) { }
                  cq->Shutdown();
              }
        }

};


typedef struct{
    nfb_server * server;
    void       * fdt;
    req_base   * req[3]; //requests
} nfb_t;

/////////////////////////////////////////////////////////////
// C interface
/////////////////////////////////////////////////////////////
void * nfb_sv_create(char * addr, int * port)
{
    nfb_t * ret;

    ret = static_cast<nfb_t *>(malloc(sizeof(nfb_t)));
    if (ret == NULL) {
        return NULL;
    }

    try {
        //create
        ret->server = new nfb_server();
        if (!(ret->server->server_run(addr, port))) {
            delete ret->server;
            free(ret);
            return NULL;
        }

        for (int unsigned it = 0; it < 3; it++) {
            req_base * rpc;
            switch (it) {
                case 0:
                    rpc = new req_fdt(ret->req + it);
                    break;

                case 1:
                    rpc = new req_read(ret->req + it);
                    break;
                case 2:
                    rpc = new req_write(ret->req + it);
                    break;
                default :
                    rpc = NULL;
                    break;
            }
            rpc->process_register(&(ret->server->service), (ret->server->cq).get());
            ret->req[it] = rpc;
        }
    }
    catch (...) {
        free(ret);
        ret = NULL;
    }
    return ret;
}


void nfb_sv_close(void * mq_id)
{
    nfb_t * ptr = static_cast<nfb_t *>(mq_id);

    delete ptr->server;
    for (int unsigned it = 0; it < 3; it++) {
        delete ptr->req[it];
    }
    free(ptr->fdt);
    free(ptr);
}


int nfb_sv_set_fdt(void * mq_id, const svOpenArrayHandle out)
{
    nfb_t * ret = static_cast<nfb_t *>(mq_id);
    void * ptr;
    int unsigned ptr_size = 0;

    ptr      = svGetArrayPtr(out);
    ptr_size = svSizeOfArray(out);

    ret->fdt = malloc(ptr_size);
    if (ret->fdt == NULL)
    {
        return false;
    }

    memcpy(ret->fdt, ptr, ptr_size);
    for (int unsigned it = 0; it < 3; it++) {
        ret->req[it]->set_fdt(ret->fdt);
    }

    return true;
}


//return request
void * nfb_sv_cmd_get(void * id, unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset)
{

    nfb_t *  server = static_cast<nfb_t*>(id);

    void * tag;
    bool ok;
    grpc::CompletionQueue::NextStatus st_ret;
    gpr_timespec deadline;

    deadline.clock_type = GPR_TIMESPAN;
    deadline.tv_sec = 0;
    deadline.tv_nsec = 0; // NOWAIT

    try {
        while ((st_ret = server->server->cq->AsyncNext<gpr_timespec>(&tag, &ok, deadline)) == grpc::CompletionQueue::NextStatus::GOT_EVENT &&
                static_cast<req_base*>(tag)->status_get() == req_base::FINISH) {

            static_cast<req_base*>(tag)->finish();
        }

        if (st_ret == grpc::CompletionQueue::NextStatus::GOT_EVENT && ok) {
            static_cast<req_base*>(tag)->get_type(cmd, data_size, offset);
            return tag;
        } else {
            *cmd = 0;
            return NULL;
        }
    }
    catch (...) {
        std::cerr << "Cannot get type "  << std::endl;
        return NULL;
    }
}


void nfb_sv_process(void * buff, const svOpenArrayHandle out)
{
    try {
        //create fdt
        static_cast<req_base*>(buff)->process(out);
    }
    catch (...) {
        std::cerr << "Cannot finish proccesing "  << std::endl;
    }
    return;
}
//void  nfb_sv_cmd_send(void * id, const svOpenArrayHandle out);


