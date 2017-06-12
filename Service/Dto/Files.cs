using System.Collections.Generic;

namespace Service.Dto
{
    public class Files
    {
        public IEnumerable<FileData> AsnFiles { get; set; }
        public IEnumerable<FileData> AcnFiles { get; set; }
    }
}
