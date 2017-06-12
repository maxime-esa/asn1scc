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

        public static void SendError(this HttpListenerResponse @this, HttpStatusCode code)
        {
            @this.StatusCode = (int)code;
            @this.ContentType = "text/html";
            @this.ContentEncoding = Encoding.UTF8;

            var content = "Error: " + code + " " + (int)code;
            var bytes = Encoding.UTF8.GetBytes(content);

            @this.ContentLength64 = bytes.Length;
            @this.OutputStream.Write(bytes, 0, bytes.Length);
        }
    }
}
