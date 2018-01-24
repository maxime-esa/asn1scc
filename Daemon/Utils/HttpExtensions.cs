using System.Net;
using System.Runtime.Serialization.Json;
using System.Text;

namespace Daemon.Utils
{
    public static class HttpExtensions
    {
        public static T ReadJson<T>(this HttpListenerRequest @this)
        {
            var serializer = new DataContractJsonSerializer(typeof(T));
            return (T)serializer.ReadObject(@this.InputStream);
        }

        public static void SendJson<T>(this HttpListenerResponse @this, T response)
        {
            @this.StatusCode = (int)HttpStatusCode.OK;
            @this.SendChunked = true;
            @this.ContentType = "application/json";
            @this.ContentEncoding = Encoding.UTF8;


            var serializer = new DataContractJsonSerializer(typeof(T));
            serializer.WriteObject(@this.OutputStream, response);
        }

        private static void WriteText(this HttpListenerResponse @this, string text)
        {
            var bytes = Encoding.UTF8.GetBytes(text);

            @this.ContentType = "text/plain";
            @this.ContentEncoding = Encoding.UTF8;
            @this.ContentLength64 = bytes.Length;

            @this.OutputStream.Write(bytes, 0, bytes.Length);
        }

        public static void SendPlainText(this HttpListenerResponse @this, string response)
        {
            @this.StatusCode = (int)HttpStatusCode.OK;
            @this.WriteText(response);
        }

        public static void SendError(this HttpListenerResponse @this, HttpStatusCode code)
        {
            @this.StatusCode = (int)code;
            @this.WriteText("Error: " + code + " " + (int)code);
        }
    }
}
