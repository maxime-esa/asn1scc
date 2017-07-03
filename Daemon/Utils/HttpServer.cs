using System;
using System.Collections.Generic;
using System.Net;
using System.Threading;

namespace Daemon.Utils
{
    class HttpServer
    {
        public HttpServer(string uri)
        {
            listener = new HttpListener();

            listener.Prefixes.Add(uri);
        }

        public void Serve()
        {
            listener.Start();

            stopRequested = false;
            while (!stopRequested)
            {
                try
                {
                    ThreadPool.QueueUserWorkItem(ProcessRequest, listener.GetContext());
                }
                catch (HttpListenerException)
                {
                    break;
                }
            }

            listener.Abort();
            listener.Close();
        }

        public void Stop()
        {
            stopRequested = true;
            listener.Stop();
        }

        public void InstallHandler(string path, Action<HttpListenerContext> handler)
        {
            if (handlers.ContainsKey(path))
            {
                throw new ArgumentException("Handler for path: '" + path + "' already installed");
            }
            handlers[path] = handler;
        }

        private void ProcessRequest(object o)
        {
            HttpListenerContext context = (HttpListenerContext)o;
            try
            {
                var handler = handlers[context.Request.Url.AbsolutePath];
                handler.Invoke(context);
                context.Response.Close();
                context = null;
            }
            catch (KeyNotFoundException)
            {
                if (context != null)
                    context.Response.SendError(HttpStatusCode.NotFound);
            }
            catch (Exception)
            {
                if (context != null)
                    context.Response.SendError(HttpStatusCode.InternalServerError);
            }
        }

        private volatile bool stopRequested = false;
        private HttpListener listener;
        private Dictionary<string, Action<HttpListenerContext>> handlers = new Dictionary<string, Action<HttpListenerContext>>();
    }
}
