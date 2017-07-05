using System.Collections.Generic;

namespace Service.Dto
{
    public class InputFiles
    {
        public IEnumerable<FileData> AsnFiles { get; set; }
        public IEnumerable<FileData> AcnFiles { get; set; }
    }
}
